use hir_def::{
    def_id::DefId,
    module::port::PortDirection,
    subroutine::{SubroutinePort, SubroutinePortDir},
    symbol::{DefKind, DefOrigin},
};
use hir_semantics::semantics::SemanticsImpl;
use syntax::{
    SyntaxAncestors, SyntaxKind, SyntaxTokenWithParent, TokenKind,
    ast::{self, AstNode},
};
use vfs::FileId;

use super::ReferenceCategory;
use crate::{
    db::workspace_symbol_index_db::WorkspaceSymbolIndexDb,
    module_resolution::{
        resolve_instantiation_target, resolve_named_port_connection, resolve_ordered_port,
        resolve_port_metadata,
    },
    semantic_index::{ConnSide, ReferenceContext},
};

pub(crate) fn classify(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    definition: DefId,
    token: SyntaxTokenWithParent<'_>,
    context: &ReferenceContext,
) -> ReferenceCategory {
    if let ReferenceContext::ConnName { side, paired, .. } = context {
        return match side {
            ConnSide::Port => ReferenceCategory::empty(),
            ConnSide::Local => port_access(db, *paired),
        };
    }

    if !is_data_definition(db, definition) {
        return ReferenceCategory::empty();
    }

    match access_site(token) {
        AccessSite::Category(category) => category,
        AccessSite::Port(ast::PortConnection::NamedPortConnection(conn)) => {
            let port = resolve_named_port_connection(db, file_id, conn).unique();
            port_access(db, port)
        }
        AccessSite::Port(ast::PortConnection::OrderedPortConnection(conn)) => {
            port_access(db, ordered_port(db, file_id, conn))
        }
        AccessSite::Port(_) => ReferenceCategory::empty(),
        AccessSite::CallArgument(argument) => {
            call_argument_access(db, file_id, argument).unwrap_or(ReferenceCategory::READ)
        }
    }
}

pub(crate) fn is_data_definition(db: &dyn WorkspaceSymbolIndexDb, definition: DefId) -> bool {
    matches!(
        definition.kind(db),
        DefKind::Net
            | DefKind::Variable
            | DefKind::Port
            | DefKind::NonAnsiPort
            | DefKind::SubroutinePort
            | DefKind::CheckerPort
            | DefKind::ClockingSignal
            | DefKind::Param
            | DefKind::Genvar
            | DefKind::Specparam
            | DefKind::EnumMember
            | DefKind::StructMember
    )
}

enum AccessSite<'a> {
    Category(ReferenceCategory),
    Port(ast::PortConnection<'a>),
    CallArgument(ast::Argument<'a>),
}

fn access_site(token: SyntaxTokenWithParent<'_>) -> AccessSite<'_> {
    use ReferenceCategory as Access;
    use SyntaxKind as Kind;

    let mut child = token.parent;
    if !ast::Name::can_cast(child.kind()) && child.kind() != Kind::MEMBER_ACCESS_EXPRESSION {
        return AccessSite::Category(Access::empty());
    }

    while let Some(parent) = child.parent() {
        match parent.kind() {
            Kind::SCOPED_NAME
            | Kind::MEMBER_ACCESS_EXPRESSION
            | Kind::PARENTHESIZED_EXPRESSION
            | Kind::CONCATENATION_EXPRESSION
            | Kind::SIMPLE_SEQUENCE_EXPR
            | Kind::SIMPLE_PROPERTY_EXPR => {}
            Kind::ELEMENT_SELECT_EXPRESSION => {
                let select = ast::ElementSelectExpression::cast(parent).unwrap();
                if select.left().syntax() != child {
                    return AccessSite::Category(Access::READ);
                }
            }
            Kind::POSTINCREMENT_EXPRESSION
            | Kind::POSTDECREMENT_EXPRESSION
            | Kind::UNARY_PREINCREMENT_EXPRESSION
            | Kind::UNARY_PREDECREMENT_EXPRESSION => {
                return AccessSite::Category(Access::READ | Access::WRITE);
            }
            Kind::NAMED_PORT_CONNECTION | Kind::ORDERED_PORT_CONNECTION => {
                return AccessSite::Port(ast::PortConnection::cast(parent).unwrap());
            }
            Kind::PROCEDURAL_RELEASE_STATEMENT | Kind::PROCEDURAL_DEASSIGN_STATEMENT => {
                return AccessSite::Category(Access::WRITE);
            }
            Kind::ORDERED_ARGUMENT | Kind::NAMED_ARGUMENT => {
                return AccessSite::CallArgument(ast::Argument::cast(parent).unwrap());
            }
            Kind::NAMED_TYPE | Kind::PACKAGE_IMPORT_ITEM | Kind::TYPE_REFERENCE => {
                return AccessSite::Category(Access::empty());
            }
            _ => {
                if let Some(binary) = ast::BinaryExpression::cast(parent)
                    && binary.left().syntax() == child
                {
                    return AccessSite::Category(
                        assignment_operator(binary).unwrap_or(Access::READ),
                    );
                }
                return AccessSite::Category(Access::READ);
            }
        }
        child = parent;
    }
    AccessSite::Category(Access::READ)
}

fn call_argument_access(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    argument: ast::Argument<'_>,
) -> Option<ReferenceCategory> {
    use ReferenceCategory as Access;
    let invocation = ast::InvocationExpression::cast(argument.syntax().parent()?.parent()?)?;
    let args = invocation.arguments()?;
    if let Some(name) = crate::signature_help::system_identifier_of(invocation.left()) {
        let index =
            args.parameters().children().position(|arg| arg.syntax() == argument.syntax())?;
        return Some(match (name.as_str(), index) {
            ("$value$plusargs" | "$readmemh" | "$readmemb", 1) => Access::WRITE,
            _ => Access::READ,
        });
    }
    let origin = call_origin(db, file_id, invocation)?;
    let direction = if let Some(owner) = origin.as_subroutine(db) {
        argument_direction(&db.subroutine(owner).ports, args, argument)?
    } else {
        let import = origin.as_dpi_import(db)?;
        let body = db.body(import.cont_id);
        argument_direction(&body.dpi_imports[import.value].method.ports, args, argument)?
    };
    Some(match direction {
        SubroutinePortDir::Input | SubroutinePortDir::ConstRef | SubroutinePortDir::Unknown => {
            Access::READ
        }
        SubroutinePortDir::Output => Access::WRITE,
        SubroutinePortDir::Inout | SubroutinePortDir::Ref => Access::READ | Access::WRITE,
    })
}

fn call_origin(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    invocation: ast::InvocationExpression<'_>,
) -> Option<DefOrigin> {
    let sema = SemanticsImpl::new(db);
    let callee = sema.resolve_expr(file_id.into(), invocation.left())?;
    Some(sema.expr_to_def(callee).unique()?.primary_origin(db))
}

pub(crate) fn dpi_writes_arguments(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    invocation: ast::InvocationExpression<'_>,
) -> bool {
    let Some(import) = call_origin(db, file_id, invocation).and_then(|site| site.as_dpi_import(db))
    else {
        return false;
    };
    let body = db.body(import.cont_id);
    body.dpi_imports[import.value].method.ports.iter().any(|port| {
        matches!(
            port.direction,
            SubroutinePortDir::Output | SubroutinePortDir::Inout | SubroutinePortDir::Ref
        )
    })
}

fn argument_direction(
    ports: &[SubroutinePort],
    args: ast::ArgumentList<'_>,
    argument: ast::Argument<'_>,
) -> Option<SubroutinePortDir> {
    let port = match argument {
        ast::Argument::NamedArgument(named) => {
            let name = hir_def::lower_ident_opt(named.name())?;
            ports.iter().find(|port| port.name.as_ref() == Some(&name))?
        }
        ast::Argument::OrderedArgument(_) => {
            let index =
                args.parameters().children().position(|arg| arg.syntax() == argument.syntax())?;
            ports.get(index)?
        }
        ast::Argument::EmptyArgument(_) => return None,
    };
    Some(port.direction)
}

pub(crate) fn assignment_operator(binary: ast::BinaryExpression<'_>) -> Option<ReferenceCategory> {
    use ReferenceCategory as Access;
    match binary.operator_token().map(|operator| operator.kind()) {
        Some(TokenKind::EQUALS) => Some(Access::WRITE),
        Some(TokenKind::LESS_THAN_EQUALS)
            if binary.syntax().kind() == SyntaxKind::NONBLOCKING_ASSIGNMENT_EXPRESSION =>
        {
            Some(Access::WRITE)
        }
        Some(
            TokenKind::PLUS_EQUAL
            | TokenKind::MINUS_EQUAL
            | TokenKind::STAR_EQUAL
            | TokenKind::SLASH_EQUAL
            | TokenKind::PERCENT_EQUAL
            | TokenKind::AND_EQUAL
            | TokenKind::OR_EQUAL
            | TokenKind::XOR_EQUAL
            | TokenKind::LEFT_SHIFT_EQUAL
            | TokenKind::RIGHT_SHIFT_EQUAL
            | TokenKind::TRIPLE_LEFT_SHIFT_EQUAL
            | TokenKind::TRIPLE_RIGHT_SHIFT_EQUAL,
        ) => Some(Access::READ | Access::WRITE),
        _ => None,
    }
}

fn ordered_port(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    conn: ast::OrderedPortConnection<'_>,
) -> Option<DefId> {
    let instance =
        SyntaxAncestors::start_from(conn.syntax()).find_map(ast::HierarchicalInstance::cast)?;
    let index =
        instance.connections().children().position(|item| item.syntax() == conn.syntax())?;
    let instantiation = SyntaxAncestors::start_from(instance.syntax())
        .find_map(ast::HierarchyInstantiation::cast)?;
    let module = resolve_instantiation_target(db, file_id, instantiation).unique()?;
    resolve_ordered_port(db, module, index).unique()
}

fn port_access(db: &dyn WorkspaceSymbolIndexDb, port: Option<DefId>) -> ReferenceCategory {
    let Some(port) = port else {
        return ReferenceCategory::empty();
    };
    let module = db.body_with_source_map(port.container_id(db));
    match resolve_port_metadata(db, &module, &module, &port.origins(db)).and_then(|(_, dir, _)| dir)
    {
        Some(PortDirection::Input) => ReferenceCategory::READ,
        Some(PortDirection::Output) => ReferenceCategory::WRITE,
        Some(PortDirection::Inout | PortDirection::Ref) => {
            ReferenceCategory::READ | ReferenceCategory::WRITE
        }
        None => ReferenceCategory::empty(),
    }
}
