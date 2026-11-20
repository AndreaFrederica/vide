use la_arena::Idx;
use smallvec::SmallVec;
use syntax::{SyntaxToken, TokenKind, ast, ast::AstNode};

use super::{LowerModuleCtx, port::PortDirection};
use crate::{Ident, alloc_with_source, lower_ident_opt};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ModportDef {
    pub name: Option<Ident>,
    pub ports: SmallVec<[ModportPort; 4]>,
}

pub type ModportId = Idx<ModportDef>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ModportPort {
    pub name: Ident,
    pub kind: ModportPortKind,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ModportPortKind {
    Simple { dir: PortDirection },
    Explicit { dir: PortDirection, target: Option<Ident>, range: Option<[i32; 2]> },
    Concatenated { dir: PortDirection, parts: Vec<(Ident, Option<[i32; 2]>)> },
    Subroutine { dir: PortDirection },
    Clocking,
}

impl LowerModuleCtx<'_> {
    pub(crate) fn lower_modport_declaration(
        &mut self,
        modport: ast::ModportDeclaration<'_>,
    ) -> SmallVec<[ModportId; 1]> {
        let mut lowered = SmallVec::new();
        for item in modport.items().children() {
            let name = lower_ident_opt(item.name());
            let ports = self.lower_modport_ports(item);
            let _file_id = self.file_id;
            let (modports, sources) =
                (&mut self.store.data.modports, &mut self.store.sources.modport_srcs);
            let modport_id = alloc_with_source(
                &self.ast_ids,
                &self.tree,
                modports,
                sources,
                ModportDef { name, ports },
                item,
            );
            lowered.push(modport_id);
        }
        lowered
    }
}

impl LowerModuleCtx<'_> {
    fn lower_modport_ports(&mut self, item: ast::ModportItem<'_>) -> SmallVec<[ModportPort; 4]> {
        let mut ports = SmallVec::new();

        // slang models a modport item as named entries whose `ports()` members are
        // simple or subroutine port lists; each list then owns its inner ports.
        for member in item.ports().ports().children() {
            match member {
                ast::Member::ModportSimplePortList(port_list) => {
                    let dir = lower_modport_dir(port_list.direction()).unwrap_or_default();
                    for port in port_list.ports().children() {
                        if let Some(name) = lower_modport_port_name(port) {
                            let kind = match port {
                                ast::ModportPort::ModportNamedPort(_) => {
                                    ModportPortKind::Simple { dir }
                                }
                                ast::ModportPort::ModportExplicitPort(port) => {
                                    lower_explicit_port(dir, port.expr())
                                }
                                ast::ModportPort::ModportSubroutinePort(_) => continue,
                            };
                            ports.push(ModportPort { name, kind });
                        }
                    }
                }
                ast::Member::ModportSubroutinePortList(port_list) => {
                    let dir = lower_modport_subroutine_dir(port_list.import_export());
                    for port in port_list.ports().children() {
                        if let Some(name) = lower_modport_port_name(port) {
                            ports.push(ModportPort {
                                name,
                                kind: ModportPortKind::Subroutine { dir },
                            });
                        }
                    }
                }
                ast::Member::ModportClockingPort(port) => {
                    let Some(name) = lower_ident_opt(port.name()) else {
                        self.report_invalid(
                            port.syntax(),
                            "modport clocking port is missing its clocking block name",
                        );
                        continue;
                    };
                    ports.push(ModportPort { name, kind: ModportPortKind::Clocking });
                }
                unsupported => {
                    self.report_unsupported(
                        unsupported.syntax(),
                        "modport port member is not lowered",
                    );
                }
            }
        }

        ports
    }
}

fn lower_explicit_port(dir: PortDirection, expression: Option<ast::Expression<'_>>) -> ModportPortKind {
    use ast::{Expression, PrimaryExpression};
    if let Some(expression @ Expression::PrimaryExpression(PrimaryExpression::ConcatenationExpression(_))) = expression {
        let mut parts = Vec::new();
        if collect_concat(expression, &mut parts, 0).is_some() && parts.len() >= 2 {
            return ModportPortKind::Concatenated { dir, parts };
        }
    }
    match expression.and_then(operand) {
        Some((target, range)) => ModportPortKind::Explicit { dir, target: Some(target), range },
        None => ModportPortKind::Explicit { dir, target: None, range: None },
    }
}

fn collect_concat(
    expression: ast::Expression<'_>,
    parts: &mut Vec<(Ident, Option<[i32; 2]>)>,
    depth: usize,
) -> Option<()> {
    use ast::{Expression, PrimaryExpression};
    if depth >= 32 || parts.len() >= 64 {
        return None;
    }
    if let Expression::PrimaryExpression(PrimaryExpression::ConcatenationExpression(concat)) =
        expression
    {
        for child in concat.expressions().children() {
            collect_concat(child, parts, depth + 1)?;
        }
    } else {
        parts.push(operand(expression)?);
    }
    Some(())
}

fn operand(expression: ast::Expression<'_>) -> Option<(Ident, Option<[i32; 2]>)> {
    match expression {
        ast::Expression::Name(ast::Name::IdentifierName(name)) => {
            Some((lower_ident_opt(name.identifier())?, None))
        }
        ast::Expression::Name(ast::Name::IdentifierSelectName(name)) => {
            Some((lower_ident_opt(name.identifier())?, Some(fixed_selection(name)?)))
        }
        _ => None,
    }
}

fn fixed_selection(name: ast::IdentifierSelectName<'_>) -> Option<[i32; 2]> {
    let mut selectors = name.selectors().children();
    let selection = selectors.next()?.selector()?;
    if selectors.next().is_some() {
        return None;
    }
    let range = match selection {
        ast::Selector::BitSelect(bit) => [decimal_index(bit.expr())?; 2],
        ast::Selector::RangeSelect(range @ ast::RangeSelect::SimpleRangeSelect(_)) => {
            [decimal_index(range.left())?, decimal_index(range.right())?]
        }
        _ => return None,
    };
    Some(range)
}

fn decimal_index(expression: ast::Expression<'_>) -> Option<i32> {
    let (expression, sign) = match expression {
        ast::Expression::PrefixUnaryExpression(unary) => match unary.operator_token()?.kind() {
            TokenKind::PLUS => (unary.operand(), 1),
            TokenKind::MINUS => (unary.operand(), -1),
            _ => return None,
        },
        _ => (expression, 1),
    };
    let ast::Expression::PrimaryExpression(ast::PrimaryExpression::LiteralExpression(literal))
        = expression else { return None; };
    let token = literal.literal()?;
    if token.kind() != TokenKind::INTEGER_LITERAL {
        return None;
    }
    let value = i64::try_from(token.int()?.get_single_word()?).ok()?;
    i32::try_from(value * sign).ok()
}

fn lower_modport_port_name(port: ast::ModportPort<'_>) -> Option<Ident> {
    match port {
        ast::ModportPort::ModportNamedPort(port) => lower_ident_opt(port.name()),
        ast::ModportPort::ModportExplicitPort(port) => lower_ident_opt(port.name()),
        ast::ModportPort::ModportSubroutinePort(port) => {
            lower_ident_opt(rightmost_name_token(port.prototype().name()))
        }
    }
}

fn rightmost_name_token(name: ast::Name<'_>) -> Option<SyntaxToken<'_>> {
    match name {
        ast::Name::IdentifierName(name) => name.identifier(),
        ast::Name::IdentifierSelectName(name) => name.identifier(),
        ast::Name::ScopedName(name) => rightmost_name_token(name.right()),
        _ => None,
    }
}

fn lower_modport_dir(tok: Option<SyntaxToken<'_>>) -> Option<PortDirection> {
    tok.and_then(|tok| match tok.kind() {
        TokenKind::INPUT_KEYWORD => Some(PortDirection::Input),
        TokenKind::OUTPUT_KEYWORD => Some(PortDirection::Output),
        TokenKind::IN_OUT_KEYWORD => Some(PortDirection::Inout),
        TokenKind::REF_KEYWORD => Some(PortDirection::Ref),
        _ => None,
    })
}

fn lower_modport_subroutine_dir(tok: Option<SyntaxToken<'_>>) -> PortDirection {
    match tok.map(|tok| tok.kind()) {
        Some(TokenKind::EXPORT_KEYWORD) => PortDirection::Output,
        _ => PortDirection::Input,
    }
}
