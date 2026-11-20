use std::collections::VecDeque;

use base_db::salsa;
use hir_def::{
    container::OwnerRef, def_id::DefId, owner::{OwnerId, OwnerKind},
    subroutine::{SubroutineKind, SubroutinePortDir, SubroutinePortId}, symbol::DefOriginLoc,
};
use hir_semantics::semantics::{Semantics, SemanticsImpl};
use hir_ty::TypeSystem;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use syntax::{
    SyntaxElement, SyntaxKind, SyntaxNode, SyntaxTokenWithParent, TokenKind, WalkEvent,
    ast::{self, AstNode},
    has_name::HasName,
    has_text_range::HasTextRange,
    token::TokenKindExt,
};
use triomphe::Arc;
use vfs::FileId;

use crate::{
    FilePosition, FileRange,
    db::{SourceFileQueryKey, root_db::RootDb, workspace_symbol_index_db::WorkspaceSymbolIndexDb},
    definitions::DefinitionClass,
    references::{ReferenceCategory, access, search::resolve_source_range},
    semantic_index::ReferenceContext,
    semantic_target::{SemanticTarget, TargetIntent, resolve_semantic_target},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentKind {
    Continuous,
    Blocking,
    Nonblocking,
    Initialization,
    Force,
    Release,
    ProceduralAssign,
    Deassign,
    SubroutineCall,
    TaskInput,
}

impl AssignmentKind {
    fn is_procedural_override(self) -> bool {
        matches!(self, Self::Force | Self::Release | Self::ProceduralAssign | Self::Deassign)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignmentInputKind {
    Data,
    Control,
    Trigger(TriggerEdge),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TriggerEdge {
    Rising,
    Falling,
    Either,
    Change,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssignmentInput {
    pub signal: DefId,
    pub kind: AssignmentInputKind,
    pub location: FileRange,
    pub hierarchical: bool,
    pub interface_operand: Option<InterfaceOperand>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InterfaceOperand {
    formal: DefId,
    member: hir_def::Ident,
    pub path: String,
    index: Option<i32>,
    pub index_expression: Option<AssignmentValue<DefId>>,
    pub range: Option<[i32; 2]>,
    pub component: Option<[u32; 2]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HierarchicalTarget {
    pub signal: DefId,
    pub location: FileRange,
    pub interface_operand: Option<InterfaceOperand>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentRelation {
    pub kind: AssignmentKind,
    pub location: FileRange,
    pub process: Option<FileRange>,
    pub targets: Vec<DefId>,
    pub hierarchical_targets: Vec<HierarchicalTarget>,
    pub inputs: Vec<AssignmentInput>,
    pub guards: Vec<AssignmentGuard>,
    pub generate_branches: Vec<GenerateBranch>,
    pub value: Option<AssignmentValue<DefId>>,
    pub word_read: Option<(DefId, AssignmentValue<DefId>)>,
    pub field_read: Option<(DefId, String)>,
    pub target_field: Option<(DefId, String)>,
    pub target_range: Option<[i32; 2]>,
    pub target_index: Option<AssignmentValue<DefId>>,
    pub target_element_index: Option<AssignmentValue<DefId>>,
    pub target_indexed_part: Option<IndexedPartSelect>,
    pub has_unresolved_operands: bool,
    pub unresolved_control_only: bool,
    unresolved_effects: Vec<TraceLimit>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateLabel {
    pub name: String,
    pub source: FileRange,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GenerateBranch {
    pub selected: Option<GenerateLabel>,
    pub alternatives: Vec<GenerateLabel>,
    pub loop_scope: bool,
    pub loop_variable: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "op", content = "args", rename_all = "camelCase")]
pub enum AssignmentValue<T> {
    Signal(T),
    ScopedSignal(T, u32),
    ScopedSelect(T, u32, i32, i32),
    ScopedComponent(T, u32, u32, Option<[i32; 2]>),
    GenerateIndex(String),
    UnsignedBit(bool),
    FillBit(bool),
    FillUnknown(char),
    Literal(String, bool),
    Select(T, i32, i32),
    BoundSelect(T, Box<Self>, Box<Self>),
    BitSelect(T, Box<Self>),
    IndexedPartSelect(T, Box<Self>, IndexedPartSelect),
    Concat(Vec<Self>),
    Cast(Option<u32>, bool, bool, Box<Self>),
    Unary(ValueUnary, Box<Self>),
    Binary(ValueBinary, Box<Self>, Box<Self>),
    Conditional(Box<Self>, Box<Self>, Box<Self>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct IndexedPartSelect {
    pub width: u32,
    pub ascending_indices: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ValueUnary {
    BitNot,
    Negate,
    Not,
    ReduceAnd,
    ReduceOr,
    ReduceXor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ValueBinary {
    BitAnd,
    BitOr,
    BitXor,
    And,
    Or,
    Equal,
    NotEqual,
    CaseEqual,
    CaseNotEqual,
    CaseItemEqual,
    CaseItemZ,
    CaseItemX,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    ShiftLeft,
    ShiftRight,
    ArithmeticShiftRight,
}

impl<T> AssignmentValue<T> {
    pub fn try_map<U>(self, convert: &impl Fn(T) -> Option<U>) -> Option<AssignmentValue<U>> {
        Some(match self {
            Self::Signal(value) => AssignmentValue::Signal(convert(value)?),
            Self::ScopedSignal(value, offset) => {
                AssignmentValue::ScopedSignal(convert(value)?, offset)
            }
            Self::ScopedSelect(value, offset, left, right) => {
                AssignmentValue::ScopedSelect(convert(value)?, offset, left, right)
            }
            Self::ScopedComponent(value, offset, component, range) => {
                AssignmentValue::ScopedComponent(convert(value)?, offset, component, range)
            }
            Self::GenerateIndex(name) => AssignmentValue::GenerateIndex(name),
            Self::UnsignedBit(value) => AssignmentValue::UnsignedBit(value),
            Self::FillBit(value) => AssignmentValue::FillBit(value),
            Self::FillUnknown(value) => AssignmentValue::FillUnknown(value),
            Self::Literal(bits, signed) => AssignmentValue::Literal(bits, signed),
            Self::Select(value, left, right) => {
                AssignmentValue::Select(convert(value)?, left, right)
            }
            Self::BoundSelect(value, left, right) => AssignmentValue::BoundSelect(
                convert(value)?, Box::new(left.try_map(convert)?), Box::new(right.try_map(convert)?),
            ),
            Self::BitSelect(value, index) => {
                AssignmentValue::BitSelect(convert(value)?, Box::new(index.try_map(convert)?))
            }
            Self::IndexedPartSelect(value, index, part) => {
                AssignmentValue::IndexedPartSelect(convert(value)?, Box::new(index.try_map(convert)?), part)
            }
            Self::Concat(parts) => AssignmentValue::Concat(
                parts.into_iter().map(|part| part.try_map(convert)).collect::<Option<_>>()?,
            ),
            Self::Cast(width, signed, two_state, value) => {
                AssignmentValue::Cast(width, signed, two_state, Box::new(value.try_map(convert)?))
            }
            Self::Unary(op, value) => AssignmentValue::Unary(op, Box::new(value.try_map(convert)?)),
            Self::Binary(op, left, right) => AssignmentValue::Binary(
                op,
                Box::new(left.try_map(convert)?),
                Box::new(right.try_map(convert)?),
            ),
            Self::Conditional(condition, yes, no) => AssignmentValue::Conditional(
                Box::new(condition.try_map(convert)?),
                Box::new(yes.try_map(convert)?),
                Box::new(no.try_map(convert)?),
            ),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssignmentGuard {
    pub location: FileRange,
    pub taken_when_true: bool,
    pub expression: Option<GuardExpression<DefId>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", content = "args", rename_all = "camelCase")]
pub enum GuardExpression<T> {
    Signal(T),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Value(AssignmentValue<T>),
}

impl<T> GuardExpression<T> {
    pub fn try_map<U>(self, convert: &impl Fn(T) -> Option<U>) -> Option<GuardExpression<U>> {
        Some(match self {
            Self::Signal(value) => GuardExpression::Signal(convert(value)?),
            Self::Value(value) => GuardExpression::Value(value.try_map(convert)?),
            Self::Not(value) => GuardExpression::Not(Box::new(value.try_map(convert)?)),
            Self::And(left, right) => GuardExpression::And(
                Box::new(left.try_map(convert)?),
                Box::new(right.try_map(convert)?),
            ),
            Self::Or(left, right) => GuardExpression::Or(
                Box::new(left.try_map(convert)?),
                Box::new(right.try_map(convert)?),
            ),
        })
    }
}

/// Direct assignment relationships in the file containing the query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileSignalRelations {
    pub signal: DefId,
    pub drivers: Vec<AssignmentRelation>,
    pub loads: Vec<AssignmentRelation>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceDirection {
    Drivers,
    Loads,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceBudget {
    pub max_depth: usize,
    pub max_signals: usize,
    pub max_assignments: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceLimit {
    HierarchicalLoad(FileRange, Option<InterfaceArrayAccess>),
    HierarchicalWrite(FileRange, Option<InterfaceArrayAccess>),
    ProceduralOverride(FileRange),
    SubroutineEffects(FileRange),
    RuntimeInput(FileRange),
    ProceduralLoop(FileRange),
    ProceduralTiming(FileRange),
    VirtualInterfaceBinding(FileRange),
    UpdateEvaluation(FileRange),
    Depth,
    Signals,
    Assignments,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceArrayAccess {
    pub formal: FileRange,
    pub member_path: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceFrontier {
    pub signal: DefId,
    pub reason: TraceLimit,
}

/// Reachable assignment relationships within one source file.
///
/// Coverage is limited to the assignment forms collected in this module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileAssignmentTrace {
    pub root: DefId,
    pub direction: TraceDirection,
    pub signals: Vec<TraceSignal>,
    pub assignments: Vec<AssignmentRelation>,
    pub frontier: Vec<TraceFrontier>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceSignal {
    pub def: DefId,
    pub name: String,
    pub declaration: Option<FileRange>,
    pub signed: Option<bool>,
    pub packed_struct: Option<FileRange>,
    pub lexical_scope: Vec<String>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct FileAssignmentIndex {
    assignments: Vec<AssignmentRelation>,
    drivers: FxHashMap<DefId, Vec<usize>>,
    loads: FxHashMap<DefId, Vec<usize>>,
}

type GenericInterfaceTypes = [(DefId, DefId, Option<hir_def::Ident>)];
pub type GenericInterfaceSource = (FilePosition, FilePosition, Option<String>);

fn resolve_interface_members(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    formal: DefId,
    member: &hir_def::Ident,
) -> Option<Vec<(DefId, Option<[i32; 2]>)>> {
    if let Some((_, interface, modport)) = bindings.iter().find(|(port, _, _)| *port == formal) {
        hir_def::pathres::resolve_generic_interface_operand(db, formal, *interface, modport.as_ref(), member)
    } else {
        hir_def::pathres::resolve_interface_operand(db, formal, member)
    }
}

impl FileAssignmentIndex {
    fn insert(&mut self, relation: AssignmentRelation) {
        let index = self.assignments.len();
        for &signal in &relation.targets {
            self.drivers.entry(signal).or_default().push(index);
        }
        let mut seen = FxHashSet::default();
        for input in &relation.inputs {
            if seen.insert(input.signal) {
                self.loads.entry(input.signal).or_default().push(index);
            }
        }
        self.assignments.push(relation);
    }

    fn lookup(&self, map: &FxHashMap<DefId, Vec<usize>>, signal: DefId) -> Vec<AssignmentRelation> {
        map.get(&signal).into_iter().flatten().map(|&id| self.assignments[id].clone()).collect()
    }
}

pub(crate) fn file_signal_relations(
    db: &RootDb,
    position: FilePosition,
) -> Option<FileSignalRelations> {
    let signal = resolve_signal(db, position)?;
    let index = file_assignment_index(db, SourceFileQueryKey::new(db, position.file_id), Vec::new(), None)?;
    Some(FileSignalRelations {
        signal,
        drivers: index.lookup(&index.drivers, signal),
        loads: index.lookup(&index.loads, signal),
    })
}

pub(crate) fn trace_file_assignments(
    db: &RootDb,
    position: FilePosition,
    direction: TraceDirection,
    budget: TraceBudget,
    interface_member: Option<&str>,
) -> Option<FileAssignmentTrace> {
    trace_bound_assignments(db, position, direction, budget, interface_member.map(|member| (member, None)), &[])
}

pub(crate) fn trace_bound_assignments(
    db: &RootDb,
    position: FilePosition,
    direction: TraceDirection,
    budget: TraceBudget,
    interface_member: Option<(&str, Option<&str>)>,
    interface_types: &[GenericInterfaceSource],
) -> Option<FileAssignmentTrace> {
    let mut bindings = interface_types
        .iter()
        .filter_map(|(formal, interface, actual_modport)| {
            let formal = resolve_definition(db, *formal)?;
            let (_, named, modport) = formal.interface_port(db)?;
            let interface = resolve_definition(db, *interface)?;
            (named.is_none() && modport.is_none() && interface.kind(db) == hir_def::symbol::DefKind::Interface)
                .then(|| (formal, interface, actual_modport.as_deref().map(hir_def::Ident::new)))
        })
        .collect::<Vec<_>>();
    bindings.sort_unstable();
    bindings.dedup();
    if bindings.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return None;
    }
    let selection = if let Some((member, backing)) = interface_member {
        let formal = resolve_definition(db, position)?;
        let (index, member) = if let Some(element) = member.strip_prefix('[') {
            let (index, member) = element.split_once("].")?;
            (Some(index.parse::<i32>().ok()?), member)
        } else {
            (None, member)
        };
        let member = hir_def::Ident::new(member);
        let members = resolve_interface_members(db, &bindings, formal, &member)?;
        let root = if let Some(backing) = backing {
            let mut matches = members.into_iter().filter_map(|(signal, _)| {
                (signal.name(db)?.as_str() == backing).then_some(signal)
            });
            let root = matches.next()?;
            if matches.any(|other| other != root) {
                return None;
            }
            root
        } else {
            let [(root, _)] = members.as_slice() else { return None; };
            *root
        };
        Some((root, formal, member, index))
    } else {
        None
    };
    let root = match &selection {
        Some((root, _, _, _)) => *root,
        None => resolve_signal(db, position)?,
    };
    let index = file_assignment_index(db, SourceFileQueryKey::new(db, position.file_id), bindings, None)?;
    let relations = match direction {
        TraceDirection::Drivers => &index.drivers,
        TraceDirection::Loads => &index.loads,
    };
    let mut trace = FileAssignmentTrace {
        root,
        direction,
        signals: Vec::new(),
        assignments: Vec::new(),
        frontier: Vec::new(),
    };
    let mut queued = FxHashSet::from_iter([root]);
    let mut emitted_signals = FxHashSet::from_iter([root]);
    let mut pending = VecDeque::from([(root, 0)]);
    let mut included = FxHashSet::default();
    let mut omitted = Vec::new();
    while let Some((signal, depth)) = pending.pop_front() {
        db.unwind_if_revision_cancelled();
        let Some(ids) = relations.get(&signal) else {
            continue;
        };
        for &id in ids {
            if included.contains(&id) {
                continue;
            }
            let relation = &index.assignments[id];
            if let Some((_, formal, member, index)) = selection.as_ref().filter(|_| signal == root) {
                let matches = |operand: Option<&InterfaceOperand>| {
                    operand.is_some_and(|operand| {
                        operand.formal == *formal
                            && operand.member == *member
                            && (operand.index == *index && operand.index_expression.is_none()
                                || index.is_some() && operand.index_expression.is_some())
                    })
                };
                let relevant = match direction {
                    TraceDirection::Drivers => relation.hierarchical_targets.iter().any(|target| {
                        target.signal == signal && matches(target.interface_operand.as_ref())
                    }),
                    TraceDirection::Loads => relation.inputs.iter().any(|input| {
                        input.signal == signal && matches(input.interface_operand.as_ref())
                    }),
                };
                if !relevant {
                    continue;
                }
            } else if direction == TraceDirection::Drivers
                && relation.hierarchical_targets.iter().any(|target| target.signal == signal)
                && !relation.hierarchical_targets.iter().any(|target| {
                    target.signal == signal
                        && target.location.file_id == position.file_id
                        && target.location.range.contains(position.offset)
                })
            {
                for target in
                    relation.hierarchical_targets.iter().filter(|target| target.signal == signal)
                {
                    let stop = TraceFrontier {
                        signal,
                        reason: TraceLimit::HierarchicalWrite(
                            target.location,
                            interface_array_access(db, target.interface_operand.as_ref()),
                        ),
                    };
                    if !trace.frontier.contains(&stop) {
                        trace.frontier.push(stop);
                    }
                }
                continue;
            } else if direction == TraceDirection::Loads
                && !relation
                    .inputs
                    .iter()
                    .any(|input| input.signal == signal && !input.hierarchical)
            {
                for input in relation
                    .inputs
                    .iter()
                    .filter(|input| input.signal == signal && input.hierarchical)
                {
                    let stop = TraceFrontier {
                        signal,
                        reason: TraceLimit::HierarchicalLoad(
                            input.location,
                            interface_array_access(db, input.interface_operand.as_ref()),
                        ),
                    };
                    if !trace.frontier.contains(&stop) {
                        trace.frontier.push(stop);
                    }
                }
                continue;
            }
            let new_signals = relation
                .targets
                .iter()
                .copied()
                .chain(relation.inputs.iter().map(|input| input.signal))
                .filter(|signal| !emitted_signals.contains(signal))
                .collect::<FxHashSet<_>>();
            let connected = match direction {
                TraceDirection::Drivers => relation
                    .inputs
                    .iter()
                    .filter(|input| !input.hierarchical)
                    .map(|input| input.signal)
                    .collect::<Vec<_>>(),
                TraceDirection::Loads => relation
                    .targets
                    .iter()
                    .copied()
                    .filter(|target| {
                        !relation
                            .hierarchical_targets
                            .iter()
                            .any(|operand| operand.signal == *target)
                    })
                    .collect(),
            };
            let limit = if depth >= budget.max_depth {
                Some(TraceLimit::Depth)
            } else if trace.assignments.len() >= budget.max_assignments {
                Some(TraceLimit::Assignments)
            } else if emitted_signals.len() + new_signals.len() > budget.max_signals.max(1) {
                Some(TraceLimit::Signals)
            } else {
                None
            };
            if let Some(reason) = limit {
                omitted.push((id, TraceFrontier { signal, reason }));
                continue;
            }
            included.insert(id);
            emitted_signals.extend(new_signals);
            trace.assignments.push(relation.clone());
            if relation.kind.is_procedural_override() {
                trace.frontier.push(TraceFrontier {
                    signal,
                    reason: TraceLimit::ProceduralOverride(relation.location),
                });
            }
            trace.frontier.extend(
                relation.unresolved_effects.iter().cloned().map(|reason| TraceFrontier { signal, reason }),
            );
            for next in connected {
                if queued.insert(next) {
                    pending.push_back((next, depth + 1));
                }
            }
        }
    }
    for (id, frontier) in omitted {
        if !included.contains(&id) && !trace.frontier.contains(&frontier) {
            trace.frontier.push(frontier);
        }
    }
    let mut signals = emitted_signals.into_iter().collect::<Vec<_>>();
    signals.sort_unstable();
    trace.signals = signals.into_iter().map(|def| trace_signal(db, def)).collect();
    Some(trace)
}

pub(crate) fn module_assignments(
    db: &RootDb,
    file_id: FileId,
    module: &str,
    budget: TraceBudget,
) -> Option<(Vec<TraceSignal>, Vec<AssignmentRelation>, bool)> {
    let index = file_assignment_index(
        db, SourceFileQueryKey::new(db, file_id), Vec::new(), Some(module.to_owned()),
    )?;
    let mut signals = FxHashSet::default();
    let mut assignments = Vec::new();
    let mut truncated = false;
    for relation in &index.assignments {
        db.unwind_if_revision_cancelled();
        if assignments.len() >= budget.max_assignments {
            truncated = true;
            break;
        }
        let new_signals = relation.targets.iter().copied()
            .chain(relation.inputs.iter().map(|input| input.signal))
            .filter(|signal| !signals.contains(signal))
            .collect::<FxHashSet<_>>();
        if signals.len() + new_signals.len() > budget.max_signals {
            truncated = true;
            continue;
        }
        signals.extend(new_signals);
        assignments.push(relation.clone());
    }
    let mut signals = signals.into_iter().collect::<Vec<_>>();
    signals.sort_unstable();
    Some((signals.into_iter().map(|def| trace_signal(db, def)).collect(), assignments, truncated))
}

fn trace_signal(db: &dyn WorkspaceSymbolIndexDb, def: DefId) -> TraceSignal {
    TraceSignal {
        def,
        signed: TypeSystem::new(db).packed_signedness_of_def(def),
        lexical_scope: trace_lexical_scope(db, def),
        packed_struct: TypeSystem::new(db).package_packed_struct(def).and_then(|typedef| {
            let source = typedef.declaration_origin(db).name_range(db)?;
            let (file_id, range) = resolve_source_range(db, source.file_id, source.value)?;
            Some(FileRange { file_id, range })
        }),
        name: def.name(db).map(|name| name.to_string()).unwrap_or_default(),
        declaration: def.declaration_origin(db).name_range(db).and_then(|source| {
            let (file_id, range) = resolve_source_range(db, source.file_id, source.value)?;
            Some(FileRange { file_id, range })
        }),
    }
}

fn trace_lexical_scope(db: &dyn WorkspaceSymbolIndexDb, def: DefId) -> Vec<String> {
    let mut scope = Vec::new();
    let mut owner = def.declaration_origin(db).container_id(db);
    while matches!(owner.kind(db), OwnerKind::Block | OwnerKind::ProceduralBlock | OwnerKind::Subroutine) {
        if let Some(name) = owner.name(db) {
            scope.push(name.to_string());
        }
        let Some(parent) = owner.parent(db) else { break };
        owner = parent;
    }
    scope.reverse();
    scope
}

fn resolve_signal(db: &RootDb, position: FilePosition) -> Option<DefId> {
    let signal = resolve_definition(db, position)?;
    access::is_data_definition(db, signal).then_some(signal)
}

fn interface_array_access(
    db: &RootDb,
    operand: Option<&InterfaceOperand>,
) -> Option<InterfaceArrayAccess> {
    let operand = operand?;
    operand.index?;
    let source = operand.formal.declaration_origin(db).name_range(db)?;
    let (file_id, range) = resolve_source_range(db, source.file_id, source.value)?;
    Some(InterfaceArrayAccess {
        formal: FileRange { file_id, range },
        member_path: operand.path.clone(),
    })
}

fn resolve_definition(
    db: &RootDb,
    FilePosition { file_id, offset }: FilePosition,
) -> Option<DefId> {
    let sema = Semantics::new(db);
    let parsed = sema.parse_file(file_id);
    let root = parsed.root();
    let target =
        resolve_semantic_target(db, file_id, offset, root, crate::token::navigation_precedence);
    let SemanticTarget::Source(target) = target.unique_for_intent(TargetIntent::FindReferences)?
    else {
        return None;
    };
    let mut definitions = target
        .into_tokens()
        .into_iter()
        .filter_map(|token| trace_definition(db, &[], file_id, token))
        .map(|class| match class {
            DefinitionClass::Definition(def) => def,
            DefinitionClass::PortConnShorthand { local, .. } => local,
        })
        .collect::<Vec<_>>();
    definitions.sort_unstable();
    definitions.dedup();
    let [signal] = definitions.as_slice() else {
        return None;
    };
    Some(*signal)
}

#[salsa::tracked(lru = 64, returns(clone))]
fn file_assignment_index(
    db: &dyn WorkspaceSymbolIndexDb,
    key: SourceFileQueryKey,
    bindings: Vec<(DefId, DefId, Option<hir_def::Ident>)>,
    module: Option<String>,
) -> Option<Arc<FileAssignmentIndex>> {
    let bindings = &bindings;
    let file_id = key.file_id(db);
    let hir_file = file_id.into();
    let tree = db.parse(hir_file);
    let root = if let Some(module) = module {
        let mut declarations = tree.root().elem_preorder().filter_map(|event| {
            let WalkEvent::Enter(SyntaxElement::Node(node)) = event else { return None };
            let name = ast::ModuleDeclaration::cast(node)?.name()?;
            (name.raw_text().trim().trim_start_matches('\\') == module).then_some(node)
        });
        let root = declarations.next()?;
        if declarations.next().is_some() {
            return None;
        }
        root
    } else {
        tree.root()
    };
    let mut index = FileAssignmentIndex::default();
    let mut nested_modules = 0usize;
    for event in root.elem_preorder() {
        if let WalkEvent::Leave(SyntaxElement::Node(node)) = event
            && ast::ModuleDeclaration::can_cast(root.kind()) && node != root && ast::ModuleDeclaration::can_cast(node.kind())
        {
            nested_modules -= 1;
        }
        let WalkEvent::Enter(SyntaxElement::Node(node)) = event else {
            continue;
        };
        if node != root && ast::ModuleDeclaration::can_cast(root.kind())
            && ast::ModuleDeclaration::can_cast(node.kind())
        {
            nested_modules += 1;
        }
        if nested_modules != 0 {
            continue;
        }
        let relation = if let Some(binary) = ast::BinaryExpression::cast(node)
            && access::assignment_operator(binary).is_some()
        {
            assignment_relation(db, bindings, file_id, binary)
        } else if let Some(declaration) = ast::Declarator::cast(node) {
            initializer_relation(db, bindings, file_id, declaration)
        } else if let Some(operand) = increment_operand(node) {
            update_relation(db, bindings, file_id, node, operand)
        } else if let Some(statement) = ast::ProceduralDeassignStatement::cast(node) {
            let kind = if node.kind() == SyntaxKind::PROCEDURAL_RELEASE_STATEMENT {
                AssignmentKind::Release
            } else {
                AssignmentKind::Deassign
            };
            unresolved_effect_relation(db, bindings, file_id, node, kind, statement.variable(), None)
        } else if let Some(invocation) = ast::InvocationExpression::cast(node)
            && call_can_write(db, file_id, invocation)
        {
            index_task_inputs(db, bindings, file_id, invocation, &mut index);
            unresolved_effect_relation(
                db, bindings,
                file_id,
                node,
                AssignmentKind::SubroutineCall,
                ast::Expression::InvocationExpression(invocation),
                None,
            )
        } else {
            continue;
        };
        if let Some(relation) = relation {
            db.unwind_if_revision_cancelled();
            index.insert(relation);
        }
    }
    Some(Arc::new(index))
}

fn index_task_inputs(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    invocation: ast::InvocationExpression<'_>,
    index: &mut FileAssignmentIndex,
) -> Option<()> {
    let callee = local_callee(db, file_id, invocation)?;
    let task = db.subroutine(callee);
    if task.kind != SubroutineKind::Task || !task.has_body {
        return None;
    }
    let node = invocation.syntax();
    for (ordinal, argument) in invocation.arguments()?.parameters().children().enumerate() {
        let (port, value) = match argument {
            ast::Argument::OrderedArgument(argument) => (ordinal, argument.expr()),
            ast::Argument::NamedArgument(argument) => {
                let Some(name) = hir_def::lower_ident_opt(argument.name()) else { continue };
                let Some(port) = task.ports.iter().position(|port| port.name.as_ref() == Some(&name))
                    else { continue };
                let Some(value) = argument.expr() else { continue };
                (port, value)
            }
            ast::Argument::EmptyArgument(_) => continue,
        };
        if !task.ports.get(port).is_some_and(|port| port.direction == SubroutinePortDir::Input) {
            continue;
        }
        let ast::PropertyExpr::SimplePropertyExpr(value) = value else { continue };
        let ast::SequenceExpr::SimpleSequenceExpr(value) = value.expr() else { continue };
        if value.repetition().is_some() {
            continue;
        }
        let expression = value.expr();
        let Some((source_file, range)) = argument.syntax().text_range()
            .and_then(|range| resolve_source_range(db, file_id.into(), range))
            else { continue };
        let target = DefId::from_source(db, DefOriginLoc::SubroutinePort(
            OwnerRef::new(callee, SubroutinePortId(port as u32)),
        ));
        let mut relation = AssignmentRelation {
            kind: AssignmentKind::TaskInput,
            location: FileRange { file_id: source_file, range },
            process: None,
            targets: vec![target],
            hierarchical_targets: Vec::new(),
            inputs: Vec::new(),
            guards: Vec::new(),
            generate_branches: enclosing_generate_branches(file_id, node),
            value: lower_value(db, bindings, file_id, expression),
            word_read: None,
            field_read: None,
            target_field: None,
            target_range: None,
            target_index: None,
            target_element_index: None,
            target_indexed_part: None,
            has_unresolved_operands: false,
            unresolved_control_only: false,
            unresolved_effects: Vec::new(),
        };
        collect_operands(db, bindings, file_id, expression.syntax(),
            AssignmentInputKind::Data, false, &mut relation);
        collect_enclosing_controls(db, bindings, file_id, node, &mut relation);
        index.insert(relation);
    }
    Some(())
}

fn call_can_write(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    invocation: ast::InvocationExpression<'_>,
) -> bool {
    if invocation.syntax().parent().is_some_and(|parent| {
        ast::ExpressionStatement::can_cast(parent.kind())
            || ast::VoidCastedCallStatement::can_cast(parent.kind())
    }) {
        return true;
    }
    let system_name = crate::signature_help::system_identifier_of(invocation.left());
    if let Some(name) = system_name.as_deref() {
        return is_runtime_input(Some(name));
    }
    invocation.arguments().is_some() && access::dpi_writes_arguments(db, file_id, invocation)
}

fn initializer_relation(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    declaration: ast::Declarator<'_>,
) -> Option<AssignmentRelation> {
    let initializer = declaration.initializer()?;
    let node = declaration.syntax();
    let kind = match node.parent()?.kind() {
        SyntaxKind::NET_DECLARATION => AssignmentKind::Continuous,
        SyntaxKind::DATA_DECLARATION | SyntaxKind::FOR_VARIABLE_DECLARATION => {
            AssignmentKind::Initialization
        }
        _ => return None,
    };
    let token = SyntaxTokenWithParent { parent: node, tok: declaration.name()? };
    let DefinitionClass::Definition(target) =
        DefinitionClass::resolve(db, file_id.into(), token).unique()?
    else {
        return None;
    };
    let (location_file, range) = resolve_source_range(db, file_id.into(), node.text_range()?)?;
    let mut relation = AssignmentRelation {
        kind,
        location: FileRange { file_id: location_file, range },
        process: None,
        targets: vec![target],
        hierarchical_targets: Vec::new(),
        inputs: Vec::new(),
        guards: Vec::new(),
        generate_branches: enclosing_generate_branches(file_id, node),
        value: lower_value(db, bindings, file_id, initializer.expr()),
        word_read: lower_word_read(db, bindings, file_id, initializer.expr()),
        field_read: lower_field_read(db, bindings, file_id, initializer.expr()),
        target_field: None,
        target_range: None,
        target_index: None,
        target_element_index: None,
        target_indexed_part: None,
        has_unresolved_operands: false,
        unresolved_control_only: false,
        unresolved_effects: Vec::new(),
    };
    collect_operands(
        db, bindings,
        file_id,
        initializer.expr().syntax(),
        AssignmentInputKind::Data,
        false,
        &mut relation,
    );
    collect_enclosing_controls(db, bindings, file_id, node, &mut relation);
    Some(relation)
}

fn assignment_relation(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    binary: ast::BinaryExpression<'_>,
) -> Option<AssignmentRelation> {
    let node = binary.syntax();
    let parent = node.parent()?;
    let kind = match parent.kind() {
        SyntaxKind::CONTINUOUS_ASSIGN => AssignmentKind::Continuous,
        SyntaxKind::EXPRESSION_STATEMENT
            if node.kind() == SyntaxKind::NONBLOCKING_ASSIGNMENT_EXPRESSION =>
        {
            AssignmentKind::Nonblocking
        }
        SyntaxKind::EXPRESSION_STATEMENT => AssignmentKind::Blocking,
        SyntaxKind::PROCEDURAL_FORCE_STATEMENT => AssignmentKind::Force,
        SyntaxKind::PROCEDURAL_ASSIGN_STATEMENT => AssignmentKind::ProceduralAssign,
        _ if ast::ForLoopStatement::cast(parent).is_some_and(|loop_stmt| {
            loop_stmt.initializers().children().any(|init| node == init.syntax())
                || loop_stmt.steps().children().any(|step| node == step.syntax())
        }) =>
        {
            AssignmentKind::Blocking
        }
        _ => return None,
    };
    if kind.is_procedural_override() {
        return unresolved_effect_relation(
            db, bindings,
            file_id,
            node.parent()?,
            kind,
            binary.left(),
            Some(binary.right()),
        );
    }
    let (location_file, range) = resolve_source_range(db, file_id.into(), node.text_range()?)?;
    let mut relation = AssignmentRelation {
        kind,
        location: FileRange { file_id: location_file, range },
        process: None,
        targets: Vec::new(),
        hierarchical_targets: Vec::new(),
        inputs: Vec::new(),
        guards: Vec::new(),
        generate_branches: enclosing_generate_branches(file_id, node),
        value: None,
        word_read: None,
        field_read: None,
        target_field: None,
        target_range: None,
        target_index: None,
        target_element_index: None,
        target_indexed_part: None,
        has_unresolved_operands: false,
        unresolved_control_only: false,
        unresolved_effects: Vec::new(),
    };

    collect_operands(
        db, bindings,
        file_id,
        binary.left().syntax(),
        AssignmentInputKind::Data,
        true,
        &mut relation,
    );
    collect_operands(
        db, bindings,
        file_id,
        binary.right().syntax(),
        AssignmentInputKind::Data,
        false,
        &mut relation,
    );
    collect_enclosing_controls(db, bindings, file_id, node, &mut relation);
    if relation.targets.is_empty() {
        return None;
    }
    if access::assignment_operator(binary) == Some(ReferenceCategory::WRITE) {
        match lower_value(db, bindings, file_id, binary.left()) {
            Some(AssignmentValue::Signal(target) | AssignmentValue::ScopedSignal(target, _))
                if relation.targets == [target] =>
            {
                relation.value = lower_value(db, bindings, file_id, binary.right());
                relation.word_read = lower_word_read(db, bindings, file_id, binary.right());
                relation.field_read = lower_field_read(db, bindings, file_id, binary.right());
            }
            Some(AssignmentValue::Concat(parts))
                if parts.iter().enumerate().all(|(index, part)| {
                    matches!(part, AssignmentValue::ScopedComponent(_, _, component, _) if *component as usize == index)
                }) =>
            {
                relation.value = lower_value(db, bindings, file_id, binary.right());
            }
            Some(AssignmentValue::ScopedSelect(target, _, left, right))
                if relation.targets == [target] =>
            {
                relation.target_range = Some([left, right]);
                relation.value = lower_value(db, bindings, file_id, binary.right());
            }
            Some(AssignmentValue::Select(target, left, right)) if relation.targets == [target] => {
                relation.target_range = Some([left, right]);
                relation.value = lower_value(db, bindings, file_id, binary.right());
            }
            Some(AssignmentValue::BitSelect(target, index)) if relation.targets == [target] => {
                relation.target_index = Some(*index);
                relation.value = lower_value(db, bindings, file_id, binary.right());
            }
            Some(AssignmentValue::IndexedPartSelect(target, index, part))
                if relation.targets == [target] =>
            {
                relation.target_index = Some(*index);
                relation.target_indexed_part = Some(part);
                relation.value = lower_value(db, bindings, file_id, binary.right());
            }
            _ => {
                if let [target] = relation.targets.as_slice()
                    && let ast::Expression::Name(ast::Name::IdentifierSelectName(name)) = binary.left()
                    && let Some(packed_word) =
                        TypeSystem::new(db).word_index_leaves_packed_vector(*target)
                {
                    let mut selectors = name.selectors().children();
                    if let Some(ast::Selector::BitSelect(select)) =
                        selectors.next().and_then(|selector| selector.selector())
                        && let Some(element) = lower_value(db, bindings, file_id, select.expr())
                    {
                        let selection = match selectors.next() {
                            None => Some(AssignmentValue::Signal(*target)),
                            Some(inner) if packed_word && selectors.next().is_none() => {
                                inner.selector().and_then(|selector| {
                                    lower_packed_selector(*target, selector, |expr| {
                                        lower_value(db, bindings, file_id, expr)
                                    })
                                    .filter(|value| !matches!(value, AssignmentValue::BoundSelect(..)))
                                })
                            }
                            _ => None,
                        };
                        if let Some(selection) = selection {
                            match selection {
                                AssignmentValue::Select(_, left, right) => {
                                    relation.target_range = Some([left, right]);
                                }
                                AssignmentValue::BitSelect(_, index) => {
                                    relation.target_index = Some(*index);
                                }
                                AssignmentValue::IndexedPartSelect(_, index, part) => {
                                    relation.target_index = Some(*index);
                                    relation.target_indexed_part = Some(part);
                                }
                                _ => {}
                            }
                            relation.target_element_index = Some(element);
                            relation.value = lower_value(db, bindings, file_id, binary.right());
                        }
                    }
                }
            }
        }
    }
    if access::assignment_operator(binary) == Some(ReferenceCategory::WRITE)
        && let Some((signal, field)) = lower_field_read(db, bindings, file_id, binary.left())
        && relation.targets.contains(&signal)
    {
        relation.target_field = Some((signal, field));
        relation.value = lower_value(db, bindings, file_id, binary.right());
    }
    let mut seen = FxHashSet::default();
    relation.inputs.retain(|input| seen.insert(input.clone()));
    Some(relation)
}

fn increment_operand(node: SyntaxNode<'_>) -> Option<ast::Expression<'_>> {
    if let Some(prefix) = ast::PrefixUnaryExpression::cast(node) {
        return matches!(
            prefix.operator_token()?.kind(),
            TokenKind::DOUBLE_PLUS | TokenKind::DOUBLE_MINUS
        )
        .then(|| prefix.operand());
    }
    let postfix = ast::PostfixUnaryExpression::cast(node)?;
    matches!(postfix.operator_token()?.kind(), TokenKind::DOUBLE_PLUS | TokenKind::DOUBLE_MINUS)
        .then(|| postfix.operand())
}

fn update_relation(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    node: SyntaxNode<'_>,
    operand: ast::Expression<'_>,
) -> Option<AssignmentRelation> {
    let mut relation =
        unresolved_effect_relation(db, bindings, file_id, node, AssignmentKind::Blocking, operand, None)?;
    relation.unresolved_effects.push(TraceLimit::UpdateEvaluation(relation.location));
    match lower_value(db, bindings, file_id, operand) {
        Some(AssignmentValue::Select(target, left, right)) if relation.targets == [target] => {
            relation.target_range = Some([left, right]);
        }
        Some(AssignmentValue::BitSelect(target, index)) if relation.targets == [target] => {
            relation.target_index = Some(*index);
        }
        _ => {}
    }
    Some(relation)
}

fn unresolved_effect_relation(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    node: SyntaxNode<'_>,
    kind: AssignmentKind,
    target: ast::Expression<'_>,
    value: Option<ast::Expression<'_>>,
) -> Option<AssignmentRelation> {
    let (location_file, range) = resolve_source_range(db, file_id.into(), node.text_range()?)?;
    let mut relation = AssignmentRelation {
        kind,
        location: FileRange { file_id: location_file, range },
        process: None,
        targets: Vec::new(),
        hierarchical_targets: Vec::new(),
        inputs: Vec::new(),
        guards: Vec::new(),
        generate_branches: enclosing_generate_branches(file_id, node),
        value: None,
        word_read: None,
        field_read: None,
        target_field: None,
        target_range: None,
        target_index: None,
        target_element_index: None,
        target_indexed_part: None,
        has_unresolved_operands: true,
        unresolved_control_only: false,
        unresolved_effects: Vec::new(),
    };
    collect_operands(db, bindings, file_id, target.syntax(), AssignmentInputKind::Data, true, &mut relation);
    if relation.targets.is_empty() {
        return None;
    }
    if let Some(value) = value {
        collect_operands(
            db, bindings,
            file_id,
            value.syntax(),
            AssignmentInputKind::Data,
            false,
            &mut relation,
        );
    }
    collect_enclosing_controls(db, bindings, file_id, node, &mut relation);
    let mut seen = FxHashSet::default();
    relation.inputs.retain(|input| seen.insert(input.clone()));
    Some(relation)
}

fn lower_field_read(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    expression: ast::Expression<'_>,
) -> Option<(DefId, String)> {
    let ast::Expression::Name(ast::Name::ScopedName(name)) = expression else { return None };
    if name.separator()?.kind() != TokenKind::DOT {
        return None;
    }
    let ast::Name::IdentifierName(base) = name.left() else { return None };
    let ast::Name::IdentifierName(field) = name.right() else { return None };
    let token = SyntaxTokenWithParent { parent: field.syntax(), tok: field.identifier()? };
    if data_def(db, bindings, file_id, token)?.kind(db) != hir_def::symbol::DefKind::StructMember {
        return None;
    }
    let identifier = token.tok.raw_text();
    let field = identifier.trim().trim_start_matches('\\').to_owned();
    Some((identifier_def(db, bindings, file_id, base)?, field))
}

fn lower_word_read(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    expression: ast::Expression<'_>,
) -> Option<(DefId, AssignmentValue<DefId>)> {
    let ast::Expression::Name(ast::Name::IdentifierSelectName(name)) = expression else {
        return None;
    };
    let token = SyntaxTokenWithParent { parent: name.syntax(), tok: name.identifier()? };
    let signal = data_def(db, bindings, file_id, token)?;
    if TypeSystem::new(db).word_index_leaves_packed_vector(signal) != Some(true) {
        return None;
    }
    let mut selectors = name.selectors().children();
    let ast::Selector::BitSelect(select) = selectors.next()?.selector()? else {
        return None;
    };
    if selectors.next().is_some() {
        return None;
    }
    Some((signal, lower_value(db, bindings, file_id, select.expr())?))
}

fn lower_value(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    expression: ast::Expression<'_>,
) -> Option<AssignmentValue<DefId>> {
    lower_value_at_depth(db, bindings, file_id, expression, 0, false)
}

fn lower_value_at_depth(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    expression: ast::Expression<'_>,
    depth: usize,
    interface_index: bool,
) -> Option<AssignmentValue<DefId>> {
    if depth >= 32 {
        return None;
    }
    use ast::{Expression, Name, PrimaryExpression};
    let lower = |expr| lower_value_at_depth(db, bindings, file_id, expr, depth + 1, interface_index);
    let boxed = |expr| lower(expr).map(Box::new);
    match expression {
        Expression::Name(Name::IdentifierName(name)) => {
            let token = SyntaxTokenWithParent { parent: name.syntax(), tok: name.identifier()? };
            let definition = trace_definition(db, bindings, file_id, token);
            if let Some(index) = generate_index(db, token, definition.as_ref()) {
                return Some(AssignmentValue::GenerateIndex(index));
            }
            identifier_def(db, bindings, file_id, name).map(AssignmentValue::Signal)
        }
        Expression::Name(Name::ScopedName(name)) => {
            if name.separator()?.kind() != TokenKind::DOT {
                return None;
            }
            let Name::IdentifierName(component) = name.right() else { return None };
            let token =
                SyntaxTokenWithParent { parent: component.syntax(), tok: component.identifier()? };
            let (source, range) = resolve_source_range(db, file_id.into(), token.text_range()?)?;
            if source != file_id {
                return None;
            }
            let offset = range.start().into();
            if let Some((_, parts)) = compound_interface_operand(db, bindings, file_id, token) {
                return Some(AssignmentValue::Concat(parts.into_iter().enumerate().map(
                    |(component, (signal, range))| {
                        AssignmentValue::ScopedComponent(signal, offset, component as u32, range)
                    },
                ).collect()));
            }
            let def = data_def(db, bindings, file_id, token)?;
            if def.kind(db) == hir_def::symbol::DefKind::StructMember {
                return None;
            }
            let selection = interface_operand(db, bindings, file_id, token)
                .and_then(|operand| operand.range);
            Some(match selection {
                Some([left, right]) => AssignmentValue::ScopedSelect(def, offset, left, right),
                None => AssignmentValue::ScopedSignal(def, offset),
            })
        }
        Expression::Name(Name::IdentifierSelectName(name)) => {
            let mut selectors = name.selectors().children();
            let selector = selectors.next()?.selector()?;
            if selectors.next().is_some() {
                return None;
            }
            let def = data_def(
                db, bindings,
                file_id,
                SyntaxTokenWithParent { parent: name.syntax(), tok: name.identifier()? },
            )?;
            lower_select(db, def, selector, lower)
        }
        Expression::ElementSelectExpression(select) => {
            let AssignmentValue::Signal(def) = lower(select.left())? else {
                return None;
            };
            lower_select(db, def, select.select().selector()?, lower)
        }
        Expression::PrimaryExpression(PrimaryExpression::ParenthesizedExpression(inner)) => {
            lower(inner.expression())
        }
        Expression::PrimaryExpression(PrimaryExpression::LiteralExpression(literal)) => {
            let token = literal.literal()?;
            if interface_index && token.kind() == TokenKind::INTEGER_LITERAL {
                let value = i32::try_from(token.int()?.get_single_word()?).ok()?;
                return Some(AssignmentValue::Literal(format!("{value:032b}"), true));
            }
            match token.raw_text().to_ascii_lowercase().as_str() {
                "0" => Some(AssignmentValue::UnsignedBit(false)),
                "1" => Some(AssignmentValue::UnsignedBit(true)),
                "'0" => Some(AssignmentValue::FillBit(false)),
                "'1" => Some(AssignmentValue::FillBit(true)),
                "'x" => Some(AssignmentValue::FillUnknown('x')),
                "'z" => Some(AssignmentValue::FillUnknown('z')),
                _ if token.kind() == TokenKind::INTEGER_LITERAL => integer_value(token.int()?),
                _ => None,
            }
        }
        Expression::PrimaryExpression(PrimaryExpression::IntegerVectorExpression(literal)) => {
            integer_value(literal.value()?.int()?)
        }
        Expression::PrimaryExpression(PrimaryExpression::ConcatenationExpression(concat)) => {
            Some(AssignmentValue::Concat(
                concat.expressions().children().map(lower).collect::<Option<_>>()?,
            ))
        }
        Expression::CastExpression(cast) => {
            let ast::DataType::IntegerType(ty) = cast.left().as_data_type()? else {
                return None;
            };
            if ty.dimensions().children().next().is_some() {
                return None;
            }
            use ast::IntegerType::*;
            let (width, default_signed, two_state) = match ty {
                ByteType(_) => (8, true, true),
                ShortIntType(_) => (16, true, true),
                IntType(_) => (32, true, true),
                LongIntType(_) => (64, true, true),
                IntegerType(_) => (32, true, false),
                TimeType(_) => (64, false, false),
                BitType(_) => (1, false, true),
                LogicType(_) | RegType(_) => (1, false, false),
            };
            let signed = ty
                .signing()
                .map_or(default_signed, |token| token.kind() == TokenKind::SIGNED_KEYWORD);
            Some(AssignmentValue::Cast(
                Some(width),
                signed,
                two_state,
                boxed(Expression::cast(cast.right().syntax())?)?,
            ))
        }
        Expression::SignedCastExpression(cast) => {
            let inner = Expression::cast(cast.inner().syntax())?;
            let signed = match cast.signing()?.kind() {
                TokenKind::SIGNED_KEYWORD => true,
                TokenKind::UNSIGNED_KEYWORD => false,
                _ => return None,
            };
            Some(AssignmentValue::Cast(None, signed, false, boxed(inner)?))
        }
        Expression::PrefixUnaryExpression(unary) => {
            let op = match unary.operator_token()?.kind() {
                TokenKind::TILDE => ValueUnary::BitNot,
                TokenKind::PLUS => return lower(unary.operand()),
                TokenKind::MINUS => ValueUnary::Negate,
                TokenKind::EXCLAMATION => ValueUnary::Not,
                TokenKind::AND => ValueUnary::ReduceAnd,
                TokenKind::OR => ValueUnary::ReduceOr,
                TokenKind::XOR => ValueUnary::ReduceXor,
                _ => return None,
            };
            Some(AssignmentValue::Unary(op, boxed(unary.operand())?))
        }
        Expression::BinaryExpression(binary) => {
            let op = match binary.operator_token()?.kind() {
                TokenKind::AND => ValueBinary::BitAnd,
                TokenKind::OR => ValueBinary::BitOr,
                TokenKind::XOR => ValueBinary::BitXor,
                TokenKind::DOUBLE_AND => ValueBinary::And,
                TokenKind::DOUBLE_OR => ValueBinary::Or,
                TokenKind::DOUBLE_EQUALS => ValueBinary::Equal,
                TokenKind::EXCLAMATION_EQUALS => ValueBinary::NotEqual,
                TokenKind::TRIPLE_EQUALS => ValueBinary::CaseEqual,
                TokenKind::EXCLAMATION_DOUBLE_EQUALS => ValueBinary::CaseNotEqual,
                TokenKind::LESS_THAN => ValueBinary::Less,
                TokenKind::LESS_THAN_EQUALS => ValueBinary::LessEqual,
                TokenKind::GREATER_THAN => ValueBinary::Greater,
                TokenKind::GREATER_THAN_EQUALS => ValueBinary::GreaterEqual,
                TokenKind::PLUS => ValueBinary::Add,
                TokenKind::MINUS => ValueBinary::Subtract,
                TokenKind::STAR => ValueBinary::Multiply,
                TokenKind::SLASH => ValueBinary::Divide,
                TokenKind::PERCENT => ValueBinary::Modulo,
                TokenKind::LEFT_SHIFT | TokenKind::TRIPLE_LEFT_SHIFT => ValueBinary::ShiftLeft,
                TokenKind::RIGHT_SHIFT => ValueBinary::ShiftRight,
                TokenKind::TRIPLE_RIGHT_SHIFT => ValueBinary::ArithmeticShiftRight,
                _ => return None,
            };
            Some(AssignmentValue::Binary(op, boxed(binary.left())?, boxed(binary.right())?))
        }
        Expression::ConditionalExpression(conditional) => {
            let mut conditions = conditional.predicate().conditions().children();
            let condition = conditions.next()?;
            if conditions.next().is_some() || condition.matches_clause().is_some() {
                return None;
            }
            Some(AssignmentValue::Conditional(
                boxed(condition.expr())?,
                boxed(conditional.left())?,
                boxed(conditional.right())?,
            ))
        }
        _ => None,
    }
}

fn integer_value(integer: syntax::value::SVInt) -> Option<AssignmentValue<DefId>> {
    let width = integer.get_bit_width();
    if !(1..=4096).contains(&width) {
        return None;
    }
    let bits = integer.serialize(2).to_ascii_lowercase();
    if !bits.bytes().all(|bit| matches!(bit, b'0' | b'1' | b'x' | b'z'))
        || bits.is_empty()
        || bits.len() > width
    {
        return None;
    }
    let first = bits.as_bytes()[0];
    let pad = if matches!(first, b'x' | b'z') { first as char } else { '0' };
    let bits = pad.to_string().repeat(width - bits.len()) + &bits;
    Some(AssignmentValue::Literal(bits, integer.is_signed()))
}

fn lower_select<'a>(
    db: &dyn WorkspaceSymbolIndexDb,
    def: DefId,
    selector: ast::Selector<'a>,
    lower: impl Fn(ast::Expression<'a>) -> Option<AssignmentValue<DefId>>,
) -> Option<AssignmentValue<DefId>> {
    // A subscript on an unpacked or multidimensional packed array can select
    // more than one bit. The trace value format models a single packed range.
    TypeSystem::new(db).packed_signedness_of_def(def)?;
    lower_packed_selector(def, selector, lower)
}

fn lower_packed_selector<'a>(
    def: DefId,
    selector: ast::Selector<'a>,
    lower: impl Fn(ast::Expression<'a>) -> Option<AssignmentValue<DefId>>,
) -> Option<AssignmentValue<DefId>> {
    let index = |expression: ast::Expression<'_>| -> Option<i32> {
        let ast::Expression::PrimaryExpression(ast::PrimaryExpression::LiteralExpression(literal)) =
            expression
        else {
            return None;
        };
        let token = literal.literal()?;
        if token.kind() != TokenKind::INTEGER_LITERAL {
            return None;
        }
        i32::try_from(token.int()?.get_single_word()?).ok()
    };
    let (left, right) = match selector {
        ast::Selector::BitSelect(select) => {
            if let Some(bit) = index(select.expr()) {
                (bit, bit)
            } else {
                return Some(AssignmentValue::BitSelect(def, Box::new(lower(select.expr())?)));
            }
        }
        ast::Selector::RangeSelect(select @ ast::RangeSelect::SimpleRangeSelect(_)) => {
            match (index(select.left()), index(select.right())) {
                (Some(left), Some(right)) => (left, right),
                _ => return Some(AssignmentValue::BoundSelect(
                    def, Box::new(lower(select.left())?), Box::new(lower(select.right())?),
                )),
            }
        }
        ast::Selector::RangeSelect(select) => {
            let width = u32::try_from(index(select.right())?).ok()?;
            if width == 0 || width > 4096 {
                return None;
            }
            let part = IndexedPartSelect {
                width,
                ascending_indices: matches!(select, ast::RangeSelect::AscendingRangeSelect(_)),
            };
            return Some(AssignmentValue::IndexedPartSelect(def, Box::new(lower(select.left())?), part));
        }
    };
    (left.abs_diff(right) < 4096).then_some(AssignmentValue::Select(def, left, right))
}

fn enclosing_generate_branches(file_id: FileId, mut child: SyntaxNode<'_>) -> Vec<GenerateBranch> {
    let label = |node| {
        let token = ast::GenerateBlock::cast(node)?.name()?;
        Some(GenerateLabel {
            name: token.raw_text().trim().trim_start_matches('\\').to_owned(),
            source: FileRange {
                file_id,
                range: SyntaxTokenWithParent { parent: node, tok: token }.text_range()?,
            },
        })
    };
    let mut branches: Vec<GenerateBranch> = Vec::new();
    while let Some(ancestor) = child.parent() {
        if ast::ModuleDeclaration::can_cast(ancestor.kind()) {
            break;
        }
        if let Some(condition) = ast::IfGenerate::cast(ancestor) {
            let first = label(condition.block().syntax());
            let second = condition.else_clause().and_then(|part| label(part.clause().syntax()));
            let (selected, alternative) =
                if child == condition.block().syntax() { (first, second) } else { (second, first) };
            branches.push(GenerateBranch {
                selected,
                alternatives: alternative.into_iter().collect(),
                ..GenerateBranch::default()
            });
        }
        if let Some(case) = ast::CaseGenerate::cast(ancestor) {
            let mut branch = GenerateBranch::default();
            for item in case.items().children() {
                let site = match item {
                    ast::CaseItem::StandardCaseItem(item) => label(item.clause().syntax()),
                    ast::CaseItem::DefaultCaseItem(item) => label(item.clause().syntax()),
                    ast::CaseItem::PatternCaseItem(_) => None,
                };
                if item.syntax() == child {
                    branch.selected = site;
                } else {
                    branch.alternatives.extend(site);
                }
            }
            branches.push(branch);
        }
        if let Some(generate) = ast::LoopGenerate::cast(ancestor) {
            branches.push(GenerateBranch {
                selected: label(child),
                loop_scope: true,
                loop_variable: generate
                    .identifier()
                    .map(|token| token.raw_text().trim().to_owned()),
                ..GenerateBranch::default()
            });
        }
        child = ancestor;
    }
    branches.reverse();
    branches
}

fn collect_enclosing_controls(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    mut child: SyntaxNode<'_>,
    relation: &mut AssignmentRelation,
) {
    let unresolved_data = relation.has_unresolved_operands;
    while let Some(ancestor) = child.parent() {
        if matches!(
            ancestor.kind(),
            SyntaxKind::INITIAL_BLOCK
                | SyntaxKind::FINAL_BLOCK
                | SyntaxKind::ALWAYS_BLOCK
                | SyntaxKind::ALWAYS_COMB_BLOCK
                | SyntaxKind::ALWAYS_FF_BLOCK
                | SyntaxKind::ALWAYS_LATCH_BLOCK
        ) {
            relation.process = ancestor
                .text_range()
                .and_then(|range| resolve_source_range(db, file_id.into(), range))
                .map(|(file_id, range)| FileRange { file_id, range });
            break;
        }
        if let Some(conditional) = ast::ConditionalStatement::cast(ancestor)
            && child != conditional.predicate().syntax()
        {
            let predicate = conditional.predicate().syntax();
            collect_operands(db, bindings, file_id, predicate, AssignmentInputKind::Control, false, relation);
            if let Some(range) = predicate.text_range()
                && let Some((source_file, range)) = resolve_source_range(db, file_id.into(), range)
            {
                relation.guards.push(AssignmentGuard {
                    location: FileRange { file_id: source_file, range },
                    taken_when_true: child == conditional.statement().syntax(),
                    expression: guard_expression(db, bindings, file_id, conditional.predicate()),
                });
            } else {
                relation.has_unresolved_operands = true;
            }
        }
        if let Some(case) = ast::CaseStatement::cast(ancestor) {
            collect_case_controls(db, bindings, file_id, case, child, relation);
        }
        if let Some(condition) = procedural_loop_condition(ancestor, child) {
            relation.has_unresolved_operands = true;
            if let Some(condition) = condition {
                collect_operands(
                    db, bindings,
                    file_id,
                    condition,
                    AssignmentInputKind::Control,
                    false,
                    relation,
                );
            }
            if let Some((file_id, range)) = ancestor
                .text_range()
                .and_then(|range| resolve_source_range(db, file_id.into(), range))
            {
                relation
                    .unresolved_effects
                    .push(TraceLimit::ProceduralLoop(FileRange { file_id, range }));
            }
        }
        let assertion_condition = ast::ConcurrentAssertionStatement::cast(ancestor)
            .map(|assertion| assertion.property_spec().syntax())
            .or_else(|| {
                ast::ImmediateAssertionStatement::cast(ancestor)
                    .map(|assertion| assertion.expr().syntax())
            });
        if let Some(condition) = assertion_condition {
            relation.has_unresolved_operands = true;
            collect_operands(db, bindings, file_id, condition, AssignmentInputKind::Control, false, relation);
        }
        let unresolved_timing = if let Some(wait) = ast::WaitStatement::cast(ancestor) {
            Some(wait.expr().syntax())
        } else if let Some(timing) = ast::TimingControlStatement::cast(ancestor) {
            let control = timing.timing_control();
            match control {
                ast::TimingControl::EventControl(_)
                | ast::TimingControl::EventControlWithExpression(_) => {
                    collect_trigger_inputs(db, bindings, file_id, control.syntax(), relation);
                    None
                }
                _ => Some(control.syntax()),
            }
        } else {
            None
        };
        if let Some(control) = unresolved_timing {
            relation.has_unresolved_operands = true;
            collect_operands(db, bindings, file_id, control, AssignmentInputKind::Control, false, relation);
            if let Some((file_id, range)) = control
                .text_range()
                .and_then(|range| resolve_source_range(db, file_id.into(), range))
            {
                relation
                    .unresolved_effects
                    .push(TraceLimit::ProceduralTiming(FileRange { file_id, range }));
            }
        }
        child = ancestor;
    }
    relation.guards.reverse();
    relation.unresolved_control_only = !unresolved_data && relation.has_unresolved_operands;
}

fn procedural_loop_condition<'a>(
    node: SyntaxNode<'a>,
    child: SyntaxNode<'a>,
) -> Option<Option<SyntaxNode<'a>>> {
    use ast::Statement::*;
    Some(match ast::Statement::cast(node)? {
        ForLoopStatement(loop_stmt)
            if child == loop_stmt.statement().syntax()
                || loop_stmt.steps().children().any(|step| child == step.syntax()) =>
        {
            loop_stmt.stop_expr().map(|expr| expr.syntax())
        }
        LoopStatement(loop_stmt) if child == loop_stmt.statement().syntax() => {
            Some(loop_stmt.expr().syntax())
        }
        DoWhileStatement(loop_stmt) if child == loop_stmt.statement().syntax() => {
            Some(loop_stmt.expr().syntax())
        }
        ForeachLoopStatement(loop_stmt) if child == loop_stmt.statement().syntax() => {
            Some(loop_stmt.loop_list().array_name().syntax())
        }
        ForeverStatement(loop_stmt) if child == loop_stmt.statement().syntax() => None,
        _ => return None,
    })
}

fn collect_case_controls<'a>(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    case: ast::CaseStatement<'a>,
    child: SyntaxNode<'a>,
    relation: &mut AssignmentRelation,
) {
    let selector =
        case.case_keyword().filter(|_| case.matches_or_inside().is_none()).and_then(|keyword| {
            let op = match keyword.kind() {
                TokenKind::CASE_KEYWORD => ValueBinary::CaseItemEqual,
                TokenKind::CASE_Z_KEYWORD => ValueBinary::CaseItemZ,
                TokenKind::CASE_X_KEYWORD => ValueBinary::CaseItemX,
                _ => return None,
            };
            Some((op, lower_value(db, bindings, file_id, case.expr())?))
        });
    let collect = |expr: SyntaxNode<'_>, relation: &mut AssignmentRelation| {
        collect_operands(db, bindings, file_id, expr, AssignmentInputKind::Control, false, relation);
    };
    collect(case.expr().syntax(), relation);
    let default_branch = child.kind() == SyntaxKind::DEFAULT_CASE_ITEM;
    let guard_start = relation.guards.len();
    relation.has_unresolved_operands |= selector.is_none();
    for item in case.items().children() {
        match item {
            ast::CaseItem::StandardCaseItem(item) => {
                for expression in item.expressions().children() {
                    collect(expression.syntax(), relation);
                }
                let guard = selector
                    .as_ref()
                    .filter(|_| relation.guards.len() - guard_start < 32)
                    .and_then(|(op, selector)| {
                        lower_case_item_guard(
                            db, bindings,
                            file_id,
                            *op,
                            selector,
                            item,
                            item.syntax() == child,
                        )
                    });
                if let Some(guard) = guard {
                    relation.guards.push(guard);
                } else {
                    relation.has_unresolved_operands = true;
                }
            }
            ast::CaseItem::PatternCaseItem(item) => {
                relation.has_unresolved_operands = true;
                collect(item.pattern().syntax(), relation);
                if let Some(predicate) = item.expr() {
                    collect(predicate.syntax(), relation);
                }
            }
            ast::CaseItem::DefaultCaseItem(_) => {}
        }
        if item.syntax() == child && !default_branch {
            break;
        }
    }
    relation.guards[guard_start..].reverse();
}

fn lower_case_item_guard(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    op: ValueBinary,
    selector: &AssignmentValue<DefId>,
    item: ast::StandardCaseItem<'_>,
    taken_when_true: bool,
) -> Option<AssignmentGuard> {
    let first_label = item.expressions().children().next()?;
    let (source_file, range) =
        resolve_source_range(db, file_id.into(), first_label.syntax().text_range()?)?;
    let comparisons = item
        .expressions()
        .children()
        .take(33)
        .map(|label| {
            Some(GuardExpression::Value(AssignmentValue::Binary(
                op,
                Box::new(selector.clone()),
                Box::new(lower_value(db, bindings, file_id, label)?),
            )))
        })
        .collect::<Option<Vec<_>>>()?;
    if comparisons.len() > 32 {
        return None;
    }
    Some(AssignmentGuard {
        location: FileRange { file_id: source_file, range },
        expression: comparisons
            .into_iter()
            .reduce(|left, right| GuardExpression::Or(Box::new(left), Box::new(right))),
        taken_when_true,
    })
}

fn guard_expression(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    predicate: ast::ConditionalPredicate<'_>,
) -> Option<GuardExpression<DefId>> {
    let mut conditions = predicate.conditions().children();
    let condition = conditions.next()?;
    if conditions.next().is_some() || condition.matches_clause().is_some() {
        return None;
    }
    lower_guard(db, bindings, file_id, condition.expr(), 0)
}

fn lower_guard(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    expression: ast::Expression<'_>,
    depth: usize,
) -> Option<GuardExpression<DefId>> {
    if depth >= 32 {
        return None;
    }
    match expression {
        ast::Expression::Name(ast::Name::IdentifierName(name)) => {
            identifier_def(db, bindings, file_id, name).map(GuardExpression::Signal)
        }
        ast::Expression::PrimaryExpression(ast::PrimaryExpression::ParenthesizedExpression(
            expr,
        )) => lower_guard(db, bindings, file_id, expr.expression(), depth + 1),
        ast::Expression::PrefixUnaryExpression(expr)
            if expr.operator_token()?.kind() == TokenKind::EXCLAMATION =>
        {
            Some(GuardExpression::Not(Box::new(lower_guard(
                db, bindings,
                file_id,
                expr.operand(),
                depth + 1,
            )?)))
        }
        ast::Expression::BinaryExpression(expr) => {
            let operator = match expr.operator_token()?.kind() {
                TokenKind::DOUBLE_AND => GuardExpression::And,
                TokenKind::DOUBLE_OR => GuardExpression::Or,
                _ => {
                    return lower_value_at_depth(db, bindings, file_id, expression, depth, false)
                        .map(GuardExpression::Value);
                }
            };
            Some(operator(
                Box::new(lower_guard(db, bindings, file_id, expr.left(), depth + 1)?),
                Box::new(lower_guard(db, bindings, file_id, expr.right(), depth + 1)?),
            ))
        }
        // A condition and its reduction OR have the same four-state truth value.
        ast::Expression::PrefixUnaryExpression(expr)
            if expr.operator_token()?.kind() == TokenKind::OR =>
        {
            lower_guard(db, bindings, file_id, expr.operand(), depth + 1)
        }
        _ => lower_value_at_depth(db, bindings, file_id, expression, depth, false).map(GuardExpression::Value),
    }
}

fn identifier_def(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    name: ast::IdentifierName<'_>,
) -> Option<DefId> {
    data_def(db, bindings, file_id, SyntaxTokenWithParent { parent: name.syntax(), tok: name.identifier()? })
}

fn generate_index(
    db: &dyn WorkspaceSymbolIndexDb,
    token: SyntaxTokenWithParent<'_>,
    definition: Option<&DefinitionClass>,
) -> Option<String> {
    ast::IdentifierName::cast(token.parent)?;
    if definition.is_some_and(|class| {
        !matches!(class, DefinitionClass::Definition(def) if def.kind(db) == hir_def::symbol::DefKind::Genvar)
    }) {
        return None;
    }
    let text = token.tok.raw_text();
    let name = text.trim();
    let mut child = token.parent;
    while let Some(parent) = child.parent() {
        if ast::ModuleDeclaration::can_cast(parent.kind()) {
            break;
        }
        if let Some(generate) = ast::LoopGenerate::cast(parent)
            && generate.block().syntax() == child
            && generate.identifier().is_some_and(|id| id.raw_text().trim() == name)
        {
            return Some(name.to_owned());
        }
        child = parent;
    }
    None
}

fn data_def(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    token: SyntaxTokenWithParent<'_>,
) -> Option<DefId> {
    let DefinitionClass::Definition(def) = trace_definition(db, bindings, file_id, token)? else {
        return None;
    };
    access::is_data_definition(db, def).then_some(def)
}

fn trace_definition(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    token: SyntaxTokenWithParent<'_>,
) -> Option<DefinitionClass> {
    let resolved = DefinitionClass::resolve(db, file_id.into(), token);
    if !resolved.is_unresolved() {
        return resolved.unique();
    }
    let operand = interface_operand(db, bindings, file_id, token)?;
    let members = resolve_interface_members(db, bindings, operand.formal, &operand.member)?;
    let [(definition, _)] = members.as_slice() else { return None; };
    Some(DefinitionClass::Definition(*definition))
}

fn interface_operand(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    token: SyntaxTokenWithParent<'_>,
) -> Option<InterfaceOperand> {
    let name = token.parent.parent().and_then(ast::ScopedName::cast)?;
    if name.right().syntax() != token.parent || name.separator()?.kind() != TokenKind::DOT {
        return None;
    }
    let (port, identifier, selector) = match name.left() {
        ast::Name::IdentifierName(port) => (port.syntax(), port.identifier()?, None),
        ast::Name::IdentifierSelectName(port) => {
            let mut selectors = port.selectors().children();
            let ast::Selector::BitSelect(select) = selectors.next()?.selector()? else {
                return None;
            };
            if selectors.next().is_some() {
                return None;
            }
            (port.syntax(), port.identifier()?, Some(select.expr()))
        }
        _ => return None,
    };
    let formal_name = hir_def::lower_ident_opt(Some(identifier))?;
    let DefinitionClass::Definition(formal) = DefinitionClass::resolve(
        db,
        file_id.into(),
        SyntaxTokenWithParent { parent: port, tok: identifier },
    )
    .unique()?
    else {
        return None;
    };
    formal.interface_port(db)?;
    let member = hir_def::lower_ident_opt(Some(token.tok))?;
    let mut index = None;
    let mut index_expression = None;
    if let Some(selector) = selector {
        index = interface_array_index(selector);
        if index.is_none() {
            // Only elaboration constants can select an interface array element.
            index_expression = Some(
                lower_value_at_depth(db, bindings, file_id, selector, 0, true)?
                    .try_map(&|definition| (definition.kind(db) == hir_def::symbol::DefKind::Param).then_some(definition))?,
            );
        }
    }
    let path = match index {
        Some(index) => format!("{formal_name}[{index}].{member}"),
        None => format!("{formal_name}.{member}"),
    };
    let range = resolve_interface_members(db, bindings, formal, &member)
        .and_then(|members| match members.as_slice() {
            [(_, range)] => *range,
            _ => None,
        });
    Some(InterfaceOperand { formal, member, path, index, index_expression, range, component: None })
}

fn compound_interface_operand(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    token: SyntaxTokenWithParent<'_>,
) -> Option<(InterfaceOperand, Vec<(DefId, Option<[i32; 2]>)>)> {
    let operand = interface_operand(db, bindings, file_id, token)?;
    let parts = resolve_interface_members(db, bindings, operand.formal, &operand.member)?;
    (parts.len() > 1 && parts.iter().all(|(def, _)| access::is_data_definition(db, *def)))
        .then_some((operand, parts))
}

fn interface_array_index(expression: ast::Expression<'_>) -> Option<i32> {
    let (sign, expression) = match expression {
        ast::Expression::PrefixUnaryExpression(unary) => match unary.operator_token()?.kind() {
            TokenKind::PLUS => (1, unary.operand()),
            TokenKind::MINUS => (-1, unary.operand()),
            _ => return None,
        },
        _ => (1, expression),
    };
    let ast::Expression::PrimaryExpression(ast::PrimaryExpression::LiteralExpression(literal)) =
        expression
    else {
        return None;
    };
    let token = literal.literal()?;
    if token.kind() != TokenKind::INTEGER_LITERAL {
        return None;
    }
    let value = i64::try_from(token.int()?.get_single_word()?).ok()?;
    i32::try_from(value * sign).ok()
}

fn collect_trigger_inputs(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    timing: SyntaxNode<'_>,
    relation: &mut AssignmentRelation,
) {
    for event in timing.elem_preorder() {
        let WalkEvent::Enter(SyntaxElement::Node(node)) = event else {
            continue;
        };
        let Some(signal_event) = ast::SignalEventExpression::cast(node) else {
            continue;
        };
        let edge = match signal_event.edge().map(|token| token.kind()) {
            Some(TokenKind::POS_EDGE_KEYWORD) => TriggerEdge::Rising,
            Some(TokenKind::NEG_EDGE_KEYWORD) => TriggerEdge::Falling,
            Some(TokenKind::EDGE_KEYWORD) => TriggerEdge::Either,
            _ => TriggerEdge::Change,
        };
        collect_operands(
            db, bindings,
            file_id,
            signal_event.expr().syntax(),
            AssignmentInputKind::Trigger(edge),
            false,
            relation,
        );
        if let Some(iff) = signal_event.iff_clause() {
            relation.has_unresolved_operands = true;
            collect_operands(
                db, bindings,
                file_id,
                iff.expr().syntax(),
                AssignmentInputKind::Control,
                false,
                relation,
            );
        }
        if !matches!(signal_event.expr(), ast::Expression::Name(ast::Name::IdentifierName(_))) {
            relation.has_unresolved_operands = true;
        }
    }
}

fn collect_operands(
    db: &dyn WorkspaceSymbolIndexDb,
    bindings: &GenericInterfaceTypes,
    file_id: FileId,
    root: SyntaxNode<'_>,
    kind: AssignmentInputKind,
    collect_targets: bool,
    relation: &mut AssignmentRelation,
) {
    let hir_file = file_id.into();
    for event in root.elem_preorder() {
        if let WalkEvent::Enter(SyntaxElement::Node(node)) = event
            && increment_operand(node).is_some()
        {
            relation.has_unresolved_operands = true;
            if let Some((file_id, range)) =
                node.text_range().and_then(|range| resolve_source_range(db, hir_file, range))
            {
                let effect = TraceLimit::UpdateEvaluation(FileRange { file_id, range });
                if !relation.unresolved_effects.contains(&effect) {
                    relation.unresolved_effects.push(effect);
                }
            }
        }
        if let WalkEvent::Enter(SyntaxElement::Node(node)) = event
            && let Some(invocation) = ast::InvocationExpression::cast(node)
        {
            let system_name = crate::signature_help::system_identifier_of(invocation.left());
            if matches!(system_name.as_deref(), Some("$signed" | "$unsigned")) {
                continue;
            }
            relation.has_unresolved_operands = true;
            if let Some(callee) = local_callee(db, file_id, invocation) {
                collect_subroutine_reads(db, callee, kind, relation);
            }
            if let Some((file_id, range)) =
                node.text_range().and_then(|range| resolve_source_range(db, hir_file, range))
            {
                let site = FileRange { file_id, range };
                let effect = if is_runtime_input(system_name.as_deref()) {
                    TraceLimit::RuntimeInput(site)
                } else {
                    TraceLimit::SubroutineEffects(site)
                };
                if !relation.unresolved_effects.contains(&effect) {
                    relation.unresolved_effects.push(effect);
                }
            }
        }
        let WalkEvent::Enter(SyntaxElement::Token(token)) = event else {
            continue;
        };
        if !token.kind().name_like() {
            continue;
        }
        if let Some(name) = virtual_interface_access(db, file_id, token) {
            relation.has_unresolved_operands = true;
            if let Some((file_id, range)) =
                name.syntax().text_range().and_then(|range| resolve_source_range(db, hir_file, range))
            {
                let effect = TraceLimit::VirtualInterfaceBinding(FileRange { file_id, range });
                if !relation.unresolved_effects.contains(&effect) {
                    relation.unresolved_effects.push(effect);
                }
            }
            continue;
        }
        if let Some((operand, parts)) = compound_interface_operand(db, bindings, file_id, token) {
            let Some((file_id, range)) = token.text_range().and_then(|range| resolve_source_range(db, hir_file, range)) else {
                relation.has_unresolved_operands = true;
                continue;
            };
            let location = FileRange { file_id, range };
            let category = access::classify(db, file_id, parts[0].0, token, &ReferenceContext::Plain);
            let count = parts.len() as u32;
            for (component, (signal, range)) in parts.into_iter().enumerate() {
                let mut operand = operand.clone();
                operand.component = Some([component as u32, count]);
                operand.range = range;
                if collect_targets && category.contains(ReferenceCategory::WRITE) {
                    if !relation.targets.contains(&signal) {
                        relation.targets.push(signal);
                    }
                    relation.hierarchical_targets.push(HierarchicalTarget {
                        signal, location, interface_operand: Some(operand.clone()),
                    });
                }
                if category.contains(ReferenceCategory::READ) {
                    relation.inputs.push(AssignmentInput {
                        signal, kind, location, hierarchical: true, interface_operand: Some(operand),
                    });
                }
            }
            continue;
        }
        let definition = trace_definition(db, bindings, file_id, token);
        if generate_index(db, token, definition.as_ref()).is_some() {
            continue;
        }
        let Some(class) = definition else {
            relation.has_unresolved_operands = true;
            continue;
        };
        let DefinitionClass::Definition(signal) = class else {
            relation.has_unresolved_operands = true;
            continue;
        };
        if signal.interface_port(db).is_some() {
            continue;
        }
        let category = access::classify(db, file_id, signal, token, &ReferenceContext::Plain);
        let writes_target = collect_targets
            && category.contains(ReferenceCategory::WRITE)
            && !syntax::SyntaxAncestors::start_from(token.parent)
                .take_while(|ancestor| *ancestor != root)
                .any(|ancestor| increment_operand(ancestor).is_some());
        let hierarchical = signal.kind(db) != hir_def::symbol::DefKind::StructMember
            && token.parent.parent().and_then(ast::ScopedName::cast).is_some_and(|name| {
                name.right().syntax() == token.parent
                    && name.separator().is_some_and(|part| part.kind() == TokenKind::DOT)
            });
        let location = || {
            let (file_id, range) = resolve_source_range(db, hir_file, token.text_range()?)?;
            Some(FileRange { file_id, range })
        };
        let interface_operand =
            hierarchical.then(|| interface_operand(db, bindings, file_id, token)).flatten();
        if writes_target
            && hierarchical
            && let Some(location) = location()
        {
            relation.hierarchical_targets.push(HierarchicalTarget {
                signal,
                location,
                interface_operand: interface_operand.clone(),
            });
        }
        if writes_target && !relation.targets.contains(&signal) {
            relation.targets.push(signal);
        }
        if category.contains(ReferenceCategory::READ)
            && let Some(location) = location()
        {
            relation.inputs.push(AssignmentInput {
                signal,
                kind,
                location,
                hierarchical,
                interface_operand,
            });
        }
    }
}

fn virtual_interface_access<'a>(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    token: SyntaxTokenWithParent<'a>,
) -> Option<ast::ScopedName<'a>> {
    use hir_def::expr::data_ty::DataTy;
    let name = token.parent.parent().and_then(ast::ScopedName::cast)?;
    if name.right().syntax() != token.parent || name.separator()?.kind() != TokenKind::DOT {
        return None;
    }
    let ast::Name::IdentifierName(handle) = name.left() else {
        return None;
    };
    let handle = SyntaxTokenWithParent { parent: handle.syntax(), tok: handle.identifier()? };
    let DefinitionClass::Definition(definition) =
        DefinitionClass::resolve(db, file_id.into(), handle).unique()?
    else {
        return None;
    };
    matches!(
        definition.data_type(db),
        Some(DataTy::Unsupported(SyntaxKind::VIRTUAL_INTERFACE_TYPE))
    ).then_some(name)
}

fn is_runtime_input(system_name: Option<&str>) -> bool {
    matches!(system_name, Some("$test$plusargs" | "$value$plusargs" | "$readmemh" | "$readmemb"))
}

fn local_callee(
    db: &dyn WorkspaceSymbolIndexDb,
    file_id: FileId,
    invocation: ast::InvocationExpression<'_>,
) -> Option<OwnerId> {
    let ast::Expression::Name(ast::Name::IdentifierName(_)) = invocation.left() else {
        return None;
    };
    let sema = SemanticsImpl::new(db);
    let expression = sema.resolve_expr(file_id.into(), invocation.left())?;
    let callee = sema.expr_to_def(expression).unique()?.primary_origin(db).as_subroutine(db)?;
    let parent = callee.parent(db)?;
    if callee.file(db) != file_id.into() || parent.module_kind(db).is_none() {
        return None;
    }
    let mut caller = sema.container_for_node(file_id.into(), invocation.syntax());
    while let Some(owner) = caller {
        if owner == parent {
            return Some(callee);
        }
        caller = owner.parent(db);
    }
    None
}

fn collect_subroutine_reads(
    db: &dyn WorkspaceSymbolIndexDb,
    callee: OwnerId,
    kind: AssignmentInputKind,
    relation: &mut AssignmentRelation,
) {
    let mut pending = VecDeque::from([callee]);
    let mut seen = FxHashSet::default();
    let mut reads = FxHashSet::default();
    while let Some(owner) = pending.pop_front() {
        if !seen.insert(owner) {
            continue;
        }
        if seen.len() > 128 {
            break;
        }
        let access = local_subroutine_access(db, owner);
        pending.extend(access.callees.iter().copied());
        relation.inputs.extend(access.reads.iter().filter_map(|&(signal, location)| {
            reads.insert((signal, location)).then_some(AssignmentInput {
                signal,
                kind,
                location,
                hierarchical: false,
                interface_operand: None,
            })
        }));
    }
}

#[derive(Default, PartialEq, Eq)]
struct LocalSubroutineAccess {
    reads: Vec<(DefId, FileRange)>,
    callees: Vec<OwnerId>,
}

#[salsa::tracked(lru = 128, returns(clone))]
fn local_subroutine_access(
    db: &dyn WorkspaceSymbolIndexDb,
    callee: OwnerId,
) -> Arc<LocalSubroutineAccess> {
    let mut access = LocalSubroutineAccess::default();
    let Some(parent) = callee.parent(db) else {
        return Arc::new(access);
    };
    let hir_file = callee.file(db);
    let Some(file_id) = hir_file.source_file_id(db) else {
        return Arc::new(access);
    };
    let tree = db.parse(hir_file);
    let Some(declaration) = db.ast_id_map(hir_file).node(callee.ast_id(db), &tree) else {
        return Arc::new(access);
    };
    for event in declaration.elem_preorder().take(8192) {
        if let WalkEvent::Enter(SyntaxElement::Node(node)) = event
            && let Some(invocation) = ast::InvocationExpression::cast(node)
            && let Some(target) = local_callee(db, file_id, invocation)
            && !access.callees.contains(&target)
        {
            access.callees.push(target);
        }
        let WalkEvent::Enter(SyntaxElement::Token(token)) = event else {
            continue;
        };
        if !token.kind().name_like()
            || token.parent.parent().and_then(ast::ScopedName::cast).is_some()
        {
            continue;
        }
        let Some(DefinitionClass::Definition(signal)) = trace_definition(db, &[], file_id, token) else {
            continue;
        };
        if signal.declaration_origin(db).loc(db).container_id(db) != parent
            || !access::classify(db, file_id, signal, token, &ReferenceContext::Plain)
                .contains(ReferenceCategory::READ)
        {
            continue;
        }
        if let Some((file_id, range)) =
            token.text_range().and_then(|range| resolve_source_range(db, hir_file, range))
        {
            access.reads.push((signal, FileRange { file_id, range }));
        }
    }
    Arc::new(access)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{position, setup_marked_with_path};

    #[test]
    fn traces_arbiter_owner_and_keeps_both_continuous_drivers() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module requester(input logic request, enabled, output wire active);
    assign active = request & enabled;
endmodule
module arbiter(
    input logic clk, rst_n, accept, input logic [1:0] request,
    output wire [1:0] grant, output logic /*marker:owner*/owner_q
);
    requester hart0(request[0], rst_n, );
    requester hart1(request[1], rst_n, );
    assign grant[0] = hart0.active;
    assign grant[1] = hart1.active & !hart0.active;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) owner_q <= 0;
        else if (accept && (|grant)) owner_q <= grant[1];
    end
endmodule
module tb(
    input logic clk, rst_n, accept, input logic [1:0] /*marker:req*/request,
    output wire /*marker:selected*/selected_request
);
    wire [1:0] grant;
    arbiter dut(clk, rst_n, accept, request, grant, );
    assign selected_request = grant[0] ? request[0] : 1'bz;
    assign selected_request = grant[1] ? request[1] : 1'bz;
endmodule
"#,
            "/arbiter.sv",
        );
        let snapshot = host.make_analysis();
        let query = |marker, direction| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    direction,
                    TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        let owner = query("owner", TraceDirection::Drivers);
        let writes: Vec<_> = owner
            .assignments
            .iter()
            .filter(|assignment| assignment.targets.contains(&owner.root))
            .collect();
        assert_eq!(writes.len(), 2);
        assert!(writes.iter().all(|assignment| assignment.kind == AssignmentKind::Nonblocking));
        assert!(writes.iter().all(|assignment| assignment.inputs.iter().any(
            |input| input.kind == AssignmentInputKind::Trigger(TriggerEdge::Rising)
        )));
        let remote: Vec<_> = owner
            .assignments
            .iter()
            .flat_map(|assignment| &assignment.inputs)
            .filter(|input| input.hierarchical)
            .collect();
        assert_eq!(remote.len(), 3);
        assert!(remote.iter().all(|input| input.signal == remote[0].signal));
        assert_ne!(remote[0].location, remote[1].location);

        let selected = query("selected", TraceDirection::Drivers);
        assert_eq!(selected.assignments.len(), 2);
        assert!(selected.assignments.iter().all(|assignment| {
            assignment.kind == AssignmentKind::Continuous
                && assignment.targets == [selected.root]
        }));
        assert_ne!(selected.assignments[0].location, selected.assignments[1].location);
        assert_eq!(query("req", TraceDirection::Loads).assignments, selected.assignments);
    }

    #[test]
    fn retains_loop_indices_as_elaboration_constants() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input wire [-1:1] source, output wire [2:0] /*marker:out*/result);
    for (genvar lane = -1; lane <= 1; lane++) begin : lanes
        assign result[1-lane] = source[lane];
    end
endmodule
"#,
            "/trace.sv",
        );
        let trace = host
            .make_analysis()
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
            )
            .unwrap()
            .unwrap();
        let [assignment] = trace.assignments.as_slice() else {
            panic!("expected one syntactic assignment");
        };
        let [branch] = assignment.generate_branches.as_slice() else {
            panic!("expected the enclosing loop");
        };
        assert!(branch.loop_scope);
        assert_eq!(branch.loop_variable.as_deref(), Some("lane"));
        assert_eq!(branch.selected.as_ref().unwrap().name, "lanes");
        assert!(!assignment.has_unresolved_operands);
        assert_eq!(assignment.inputs.len(), 1);
        assert!(matches!(
            &assignment.target_index,
            Some(AssignmentValue::Binary(ValueBinary::Subtract, _, index))
                if matches!(index.as_ref(), AssignmentValue::GenerateIndex(name) if name == "lane")
        ));
        assert!(matches!(
            &assignment.value,
            Some(AssignmentValue::BitSelect(_, index))
                if matches!(index.as_ref(), AssignmentValue::GenerateIndex(name) if name == "lane")
        ));
    }

    #[test]
    fn retains_the_order_of_modport_concatenations() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic [7:4] data;
    logic [0:3] other;
    modport tx(output .pair({data[4], other[2]}));
    modport rx(input .pair({data[4], {other[2], {data[7], data[4]}}}));
endinterface
module writer(input logic [1:0] a, channel.tx /*marker:writer*/link);
    assign link.pair = a;
endmodule
module reader(channel.rx /*marker:reader*/link, output wire [3:0] /*marker:q*/q);
    assign q = link.pair;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let at = |marker| position(file, &markers, marker);
        let driver = snapshot
            .trace_file_assignments(at("q"), TraceDirection::Drivers, budget)
            .unwrap()
            .unwrap();
        let [read] = driver.assignments.as_slice() else { panic!("expected one reader") };
        let Some(AssignmentValue::Concat(parts)) = &read.value else {
            panic!("expected the ordered operands");
        };
        let ranges = parts.iter().enumerate().map(|(index, part)| match part {
            AssignmentValue::ScopedComponent(_, _, component, Some(range)) => {
                assert_eq!(*component as usize, index);
                *range
            }
            _ => panic!("expected a selected component"),
        }).collect::<Vec<_>>();
        assert_eq!(ranges, [[4, 4], [2, 2], [7, 7], [4, 4]]);
        assert_eq!(read.inputs[0].signal, read.inputs[3].signal);
        let writer = snapshot.trace_bound_assignments(
            at("writer"), TraceDirection::Drivers, budget, Some(("pair", Some("other"))), &[],
        ).unwrap().unwrap();
        let [write] = writer.assignments.as_slice() else { panic!("expected one writer") };
        assert_eq!(write.hierarchical_targets.len(), 2);
        assert_eq!(write.hierarchical_targets[1].signal, writer.root);
        assert!(matches!(write.value, Some(AssignmentValue::Signal(_))));
    }

    #[test]
    fn retains_fixed_modport_alias_read_and_write_ranges() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    wire [0:7] data;
    modport tx(output .send(data[1:2]));
    modport rx(input .receive(data[1:2]));
endinterface
module sender(input wire [1:0] a, channel.tx link);
    assign link./*marker:write*/send = a;
endmodule
module receiver(channel.rx link, output wire [1:0] /*marker:q*/q);
    assign q = link.receive;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let drivers = |marker| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        let reading = drivers("q");
        let writing = drivers("write");
        let [read] = reading.assignments.as_slice() else { panic!("expected one read") };
        let [write] = writing.assignments.as_slice() else { panic!("expected one write") };
        assert_eq!(read.inputs[0].signal, writing.root);
        assert_eq!(read.inputs[0].interface_operand.as_ref().unwrap().range, Some([1, 2]));
        assert!(matches!(read.value, Some(AssignmentValue::ScopedSelect(_, _, 1, 2))));
        assert_eq!(write.target_range, Some([1, 2]));
        assert_eq!(write.hierarchical_targets[0].interface_operand.as_ref().unwrap().range, Some([1, 2]));
    }

    #[test]
    fn tracks_members_exposed_by_named_modports() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic datum, /*marker:backing*/hidden, alias_source;
    modport tx(output datum);
    modport rx(input datum, input .alias_source(hidden), input .complex(hidden ^ datum));
endinterface
module sender(input logic a, channel.tx link);
    assign link./*marker:write*/datum = a;
endmodule
module receiver(channel.rx /*marker:formal*/link, output logic /*marker:q*/q, invalid, aliased, expression);
    assign q = link.datum;
    assign invalid = link./*marker:hidden*/hidden;
    assign aliased = link./*marker:alias*/alias_source;
    assign expression = link./*marker:complex*/complex;
endmodule
module other_receiver(channel.rx link, output logic unrelated);
    assign unrelated = link.alias_source;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let query = |marker| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    budget,
                )
                .unwrap()
        };
        let reader = query("q").unwrap();
        let [assignment] = reader.assignments.as_slice() else {
            panic!("expected the receiver assignment")
        };
        assert!(!assignment.has_unresolved_operands);
        assert_eq!(assignment.inputs.len(), 1);
        assert!(assignment.inputs[0].hierarchical);
        assert!(matches!(assignment.value, Some(AssignmentValue::ScopedSignal(_, _))));
        let writer = query("write").unwrap();
        assert_eq!(writer.root, assignment.inputs[0].signal);
        assert_eq!(writer.assignments[0].hierarchical_targets.len(), 1);
        assert!(query("hidden").is_none());
        assert_eq!(query("alias").unwrap().root, query("backing").unwrap().root);
        assert!(query("complex").is_none());
        let selected = snapshot
            .trace_interface_member(
                position(file, &markers, "formal"),
                "alias_source",
                TraceDirection::Loads,
                budget,
            )
            .unwrap()
            .unwrap();
        assert_eq!(selected.root, query("backing").unwrap().root);
        assert_eq!(selected.assignments.len(), 1);
        assert!(selected.signals.iter().any(|signal| signal.name == "aliased"));
        assert!(selected.signals.iter().all(|signal| signal.name != "unrelated"));
        assert_eq!(
            selected.assignments[0].inputs[0].interface_operand.as_ref().unwrap().path,
            "link.alias_source",
        );
    }

    #[test]
    fn traces_only_the_selected_interface_array_element() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic datum;
    modport tx(output .write_data(datum));
    modport rx(input .read_data(datum));
endinterface
module sender(input logic a, b, channel.tx /*marker:sender*/link[7:6]);
    assign link[7].write_data = a;
    assign link[6].write_data = b;
endmodule
module receiver(channel.rx /*marker:receiver*/link[-1:0], output wire /*marker:q*/q, n);
    assign q = link[-1].read_data;
    assign n = link[0].read_data;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        for (marker, direction, path, connected, unrelated) in [
            ("sender", TraceDirection::Drivers, "[7].write_data", "a", "b"),
            ("receiver", TraceDirection::Loads, "[-1].read_data", "q", "n"),
        ] {
            let trace = snapshot
                .trace_interface_member(position(file, &markers, marker), path, direction, budget)
                .unwrap()
                .unwrap();
            assert_eq!(trace.assignments.len(), 1);
            assert!(trace.signals.iter().any(|signal| signal.name == connected));
            assert!(trace.signals.iter().all(|signal| signal.name != unrelated));
        }
        let trace = snapshot
            .trace_file_assignments(position(file, &markers, "q"), TraceDirection::Drivers, budget)
            .unwrap()
            .unwrap();
        let operand = trace.assignments[0].inputs[0].interface_operand.as_ref().unwrap();
        assert_eq!(operand.path, "link[-1].read_data");
    }

    #[test]
    fn retains_signed_interface_indices_for_elaboration() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic datum;
    modport tx(output .send(datum));
    modport rx(input .read_data(datum));
endinterface
module sender(input logic [1:0] data, channel.tx /*marker:sender*/link[7:6]);
    for (genvar i = 0; i < 2; ++i) begin : drive
        assign link[7-i].send = data[i];
    end
endmodule
module receiver(channel.rx link[-1:0], output wire /*marker:q*/q);
    assign q = link[-(2-1)].read_data;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let write = snapshot
            .trace_interface_member(
                position(file, &markers, "sender"),
                "[7].send",
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        let driver = &write.assignments[0];
        let symbolic = driver.hierarchical_targets[0].interface_operand.as_ref().unwrap();
        assert!(matches!(
            symbolic.index_expression.as_ref(),
            Some(AssignmentValue::Binary(ValueBinary::Subtract, lhs, rhs))
                if matches!(lhs.as_ref(), AssignmentValue::Literal(bits, true) if bits.len() == 32)
                && matches!(rhs.as_ref(), AssignmentValue::GenerateIndex(name) if name == "i")
        ));
        assert!(driver.value.is_some());

        let read = snapshot
            .trace_file_assignments(
                position(file, &markers, "q"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        let symbolic = read.assignments[0].inputs[0].interface_operand.as_ref().unwrap();
        assert!(matches!(
            symbolic.index_expression.as_ref(),
            Some(AssignmentValue::Unary(ValueUnary::Negate, operand))
                if matches!(operand.as_ref(),
                    AssignmentValue::Binary(ValueBinary::Subtract, lhs, rhs)
                        if [lhs, rhs].iter().all(|value|
                            matches!(value.as_ref(), AssignmentValue::Literal(bits, true) if bits.len() == 32)))
        ));
    }

    #[test]
    fn keeps_interface_index_parameter_as_a_source_dependency() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic data;
    modport rx(input .receive(data));
endinterface
module reader #(parameter int BASE = 0)(channel.rx link[-1:0], output wire /*marker:q*/q);
    localparam int INDEX = BASE - 1;
    assign q = link[INDEX].receive;
endmodule
"#,
            "/trace.sv",
        );
        let trace = host
            .make_analysis()
            .trace_file_assignments(
                position(file, &markers, "q"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
            )
            .unwrap()
            .unwrap();
        let index = trace.signals.iter().find(|signal| signal.name == "INDEX").unwrap().def;
        let read = trace.assignments[0]
            .inputs
            .iter()
            .find_map(|input| input.interface_operand.as_ref())
            .unwrap();
        assert_eq!(read.index_expression, Some(AssignmentValue::Signal(index)));
        assert!(trace.assignments[0].inputs.iter().any(|input| input.signal == index));
    }

    #[test]
    fn specializes_generic_interface_members_per_instance() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface /*marker:first*/narrow; logic data; endinterface
interface /*marker:second*/alternate; wire data; endinterface
module sink(interface /*marker:formal*/link, output wire /*marker:output*/q);
    assign q = link.data;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let at = |marker| position(file, &markers, marker);
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let query = |interface| {
            snapshot.trace_bound_assignments(
                at("output"), TraceDirection::Drivers, budget, None, &[(at("formal"), at(interface), None)]
            ).unwrap().unwrap()
        };
        let first = query("first");
        let second = query("second");
        assert_ne!(first.assignments[0].inputs[0].signal, second.assignments[0].inputs[0].signal);
        assert_eq!(first, query("first"));
        for (name, trace) in [("first", first), ("second", second)] {
            let input = &trace.assignments[0].inputs[0];
            assert!(input.hierarchical);
            assert_eq!(input.interface_operand.as_ref().unwrap().path, "link.data");
            let loads = snapshot.trace_bound_assignments(
                at("formal"), TraceDirection::Loads, budget, Some(("data", None)), &[(at("formal"), at(name), None)]
            ).unwrap().unwrap();
            assert_eq!(loads.root, input.signal);
            assert!(loads.signals.iter().any(|signal| signal.name == "q"));
        }
    }

    #[test]
    fn specializes_a_generic_interface_using_only_the_bound_modport_view() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface /*marker:actual*/channel;
    wire data, hidden;
    modport rx(input .receive(data));
endinterface
module sink(interface /*marker:formal*/link, output wire /*marker:q*/q);
    assign q = link.receive;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let at = |marker| position(file, &markers, marker);
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let bindings = [(at("formal"), at("actual"), Some("rx".to_owned()))];
        let driver = snapshot
            .trace_bound_assignments(at("q"), TraceDirection::Drivers, budget, None, &bindings)
            .unwrap()
            .unwrap();
        let input = &driver.assignments[0].inputs[0];
        let member = driver.signals.iter().find(|signal| signal.def == input.signal).unwrap();
        assert_eq!(member.name, "data");
        assert_eq!(input.interface_operand.as_ref().unwrap().path, "link.receive");
        assert!(
            snapshot.trace_bound_assignments(
                at("formal"), TraceDirection::Loads, budget, Some(("hidden", None)), &bindings
            ).unwrap().is_none()
        );
    }

    #[test]
    fn hierarchical_writes_are_selected_at_their_own_source_site() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module leaf(output logic /*marker:state*/q);
endmodule
module top(input logic /*marker:input*/a, b);
    leaf left();
    leaf right();
    always_comb left./*marker:write*/q = a;
    always_comb right.q = b;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let budget = TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 };
        let query = |marker, direction| {
            snapshot
                .trace_file_assignments(position(file, &markers, marker), direction, budget)
                .unwrap()
                .unwrap()
        };
        let declaration = query("state", TraceDirection::Drivers);
        assert!(declaration.assignments.is_empty());
        assert!(
            declaration
                .frontier
                .iter()
                .any(|stop| matches!(stop.reason, TraceLimit::HierarchicalWrite(_, _)))
        );
        let source = query("write", TraceDirection::Drivers);
        let [assignment] = source.assignments.as_slice() else {
            panic!("expected only the selected write")
        };
        assert_eq!(assignment.hierarchical_targets.len(), 1);
        assert_eq!(source.signals.iter().filter(|signal| signal.name == "b").count(), 0);
        assert_eq!(
            query("input", TraceDirection::Loads).assignments.as_slice(),
            [assignment.clone()]
        );
    }

    #[test]
    fn keeps_hierarchical_read_sites_at_the_instance_boundary() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module leaf(input logic a);
    logic /*marker:state*/state;
    assign state = a;
endmodule
module top(input logic a, b, output logic /*marker:out*/q);
    leaf left(a);
    leaf right(b);
    assign q = left.state ^ right.state;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let query = |marker, direction| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    direction,
                    TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        let drivers = query("out", TraceDirection::Drivers);
        let [assignment] = drivers.assignments.as_slice() else {
            panic!("expected the local assignment")
        };
        assert_eq!(assignment.inputs.len(), 2);
        assert!(assignment.inputs.iter().all(|input| input.hierarchical));
        assert_eq!(assignment.inputs[0].signal, assignment.inputs[1].signal);
        assert_ne!(assignment.inputs[0].location, assignment.inputs[1].location);
        assert!(
            query("state", TraceDirection::Drivers).assignments[0]
                .inputs
                .iter()
                .all(|input| !input.hierarchical)
        );
        let loads = query("state", TraceDirection::Loads);
        assert!(loads.assignments.is_empty());
        assert!(
            loads
                .frontier
                .iter()
                .any(|stop| matches!(stop.reason, TraceLimit::HierarchicalLoad(_, _)))
        );
    }

    #[test]
    fn indexes_generate_assertion_actions_with_unresolved_control() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input logic clk, valid, stimulus, output logic /*marker:out*/q);
    for (genvar i = 0; i < 1; i++) begin : g
        assert property (@(posedge clk) valid) else begin
            $error("assertion failed: %b", valid);
            q = stimulus;
        end
    end
endmodule
"#,
            "/trace.sv",
        );
        let trace = host
            .make_analysis()
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
            )
            .unwrap()
            .unwrap();
        let [assignment] = trace.assignments.as_slice() else {
            panic!("expected the assignment inside the assertion action");
        };
        assert!(assignment.has_unresolved_operands);
        assert!(assignment.unresolved_control_only);
        assert!(assignment.inputs.iter().any(|input| input.kind == AssignmentInputKind::Control));
        assert!(trace.signals.iter().any(|signal| signal.name == "valid"));
        assert!(trace.signals.iter().any(|signal| signal.name == "stimulus"));
    }

    #[test]
    fn traces_increment_writes_and_keeps_index_side_effects_separate() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input bit clk, enable, data, input int seed, limit);
    int /*marker:count*/count, /*marker:cursor*/cursor, /*marker:result*/result;
    int /*marker:index*/index;
    bit [3:0] /*marker:lanes*/lanes;
    always @(posedge clk) if (enable) begin
        count++;
        result = --count;
        lanes[cursor++] = data;
        for (index = seed; index < limit; index++) lanes[1] = data;
    end
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let trace = |marker| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 1, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        let count = trace("count");
        assert_eq!(count.assignments.len(), 2);
        for assignment in &count.assignments {
            assert!(assignment.has_unresolved_operands);
            assert!(assignment.inputs.iter().any(|input| input.signal == count.root));
        }
        let result = trace("result");
        assert!(result.assignments[0].has_unresolved_operands);
        assert!(!result.assignments[0].unresolved_control_only);
        assert!(
            result
                .frontier
                .iter()
                .any(|stop| matches!(stop.reason, TraceLimit::UpdateEvaluation(_)))
        );
        let cursor = trace("cursor");
        assert_eq!(cursor.assignments.len(), 1);
        assert_eq!(cursor.assignments[0].targets, [cursor.root]);
        let lanes = trace("lanes");
        assert!(lanes.assignments.iter().all(|assignment| assignment.targets == [lanes.root]));
        let index = trace("index");
        assert_eq!(index.assignments.len(), 2);
        assert!(index.signals.iter().any(|signal| signal.name == "seed"));
        assert!(index.signals.iter().any(|signal| signal.name == "limit"));
        assert!(
            index.frontier.iter().any(|stop| matches!(stop.reason, TraceLimit::ProceduralLoop(_)))
        );
    }

    #[test]
    fn traces_procedural_timing_inputs_and_source_locations() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input int delay_ticks, input logic ready, data);
    logic /*marker:delay*/delayed, /*marker:wait*/waited;
    initial #(delay_ticks) delayed = data;
    initial wait (ready) waited = data;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        for (marker, control) in [("delay", "delay_ticks"), ("wait", "ready")] {
            let trace = snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 2, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap();
            let [assignment] = trace.assignments.as_slice() else {
                panic!("expected one assignment for {marker}");
            };
            assert!(assignment.has_unresolved_operands);
            let signal = trace.signals.iter().find(|signal| signal.name == control).unwrap();
            assert!(assignment.inputs.iter().any(|input| input.signal == signal.def
                && input.kind == AssignmentInputKind::Control));
            assert!(trace.frontier.iter().any(|stop| matches!(stop.reason,
                TraceLimit::ProceduralTiming(site)
                    if site.file_id == assignment.location.file_id
                        && site.range.end() <= assignment.location.range.start())));
        }
    }

    #[test]
    fn reports_which_virtual_interface_access_needs_a_runtime_target() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
interface channel;
    logic data;
    modport reader (input .value(data));
endinterface
module top;
    channel source();
    virtual channel.reader view_handle;
    logic /*marker:q*/q;
    initial begin
        view_handle = source.reader;
        q = /*marker:access*/view_handle.value;
    end
endmodule
"#,
            "/trace.sv",
        );
        let trace = host.make_analysis().trace_file_assignments(
            position(file, &markers, "q"),
            TraceDirection::Drivers,
            TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
        ).unwrap().unwrap();
        let access = position(file, &markers, "access");
        assert!(trace.frontier.iter().any(|item| matches!(
            item.reason, TraceLimit::VirtualInterfaceBinding(site)
                if site.file_id == access.file_id && site.range.start() == access.offset
        )));
    }

    #[test]
    fn traces_procedural_loop_controls_without_assuming_iteration_order() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input logic enabled, clk, data, input int count, input logic [1:0] lanes);
    logic /*marker:a*/q_while, /*marker:b*/q_repeat, /*marker:c*/q_do;
    logic /*marker:d*/q_foreach, /*marker:e*/q_forever, /*marker:f*/q_for;
    int /*marker:init*/index;
    always @(posedge clk) begin
        while (enabled) begin q_while = data; break; end
        repeat (count) q_repeat <= data;
        do q_do <= data; while (enabled);
        foreach (lanes[i]) q_foreach <= data;
        for (index = 0; index < count; index++) q_for <= data;
    end
    initial forever @(negedge clk) q_forever = data;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let trace = |marker| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 1, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        for (marker, condition) in [
            ("a", Some("enabled")),
            ("b", Some("count")),
            ("c", Some("enabled")),
            ("d", Some("lanes")),
            ("e", None),
            ("f", Some("count")),
        ] {
            let trace = trace(marker);
            let [assignment] = trace.assignments.as_slice() else {
                panic!("expected the {marker} assignment")
            };
            assert!(assignment.has_unresolved_operands, "{marker}");
            assert!(assignment.guards.is_empty(), "{marker}");
            assert!(
                trace
                    .frontier
                    .iter()
                    .any(|stop| matches!(stop.reason, TraceLimit::ProceduralLoop(_)))
            );
            if let Some(condition) = condition {
                let signal = trace.signals.iter().find(|signal| signal.name == condition).unwrap();
                assert!(assignment.inputs.iter().any(|input| input.signal == signal.def
                    && input.kind == AssignmentInputKind::Control));
            }
        }
        let index = trace("init");
        let initializer =
            index.assignments.iter().find(|assignment| assignment.value.is_some()).unwrap();
        let count = index.signals.iter().find(|signal| signal.name == "count").unwrap();
        assert!(!initializer.inputs.iter().any(|input| input.signal == count.def));
    }

    #[test]
    fn traces_dpi_call_writes_without_claiming_foreign_execution() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top;
    import "DPI-C" function int adjust(input int source, output int effect);
    int source, /*marker:result*/result, /*marker:effect*/effect;
    initial result = adjust(source, effect);
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        for (marker, expected) in
            [("result", AssignmentKind::Blocking), ("effect", AssignmentKind::SubroutineCall)]
        {
            let trace = snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap();
            let [assignment] = trace.assignments.as_slice() else {
                panic!("expected the {marker} relation")
            };
            assert_eq!(assignment.kind, expected);
            assert!(trace.signals.iter().any(|signal| signal.name == "source"));
            assert!(
                trace
                    .frontier
                    .iter()
                    .any(|stop| matches!(stop.reason, TraceLimit::SubroutineEffects(_)))
            );
        }
    }

    #[test]
    fn traces_runtime_plusargs_and_memory_file_writes() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top;
    int /*marker:mode*/mode;
    bit /*marker:selected*/selected;
    logic [7:0] /*marker:memory*/memory [0:7];
    initial begin
        if ($value$plusargs("MODE=%d", mode)) selected = $test$plusargs("ENABLE");
        $readmemh("stimulus.hex", memory);
    end
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let trace = |marker| {
            snapshot
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Drivers,
                    TraceBudget { max_depth: 8, max_signals: 32, max_assignments: 32 },
                )
                .unwrap()
                .unwrap()
        };
        for (marker, expected) in [("mode", 1), ("selected", 2), ("memory", 1)] {
            let trace = trace(marker);
            assert_eq!(trace.assignments.len(), 1, "{marker}");
            if marker == "mode" {
                assert!(trace.assignments[0].guards.is_empty());
            }
            assert_eq!(
                trace
                    .frontier
                    .iter()
                    .filter(|stop| matches!(stop.reason, TraceLimit::RuntimeInput(_)))
                    .count(),
                expected,
                "{marker}"
            );
        }
    }

    #[test]
    fn traces_task_call_arguments_and_reports_unresolved_subroutine_effects() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic /*marker:data*/data);
    logic /*marker:result*/result, /*marker:named*/named_result;
    logic /*marker:config*/config_bit, /*marker:expression*/expression_result;
    task automatic copy(input logic /*marker:formal*/source, output logic dest);
        dest = source ^ config_bit;
    endtask
    function automatic logic inner(input logic source);
        return source ^ config_bit;
    endfunction
    function automatic logic transform(input logic source);
        return inner(source);
    endfunction
    always_comb begin
        copy(data, result);
        copy(.dest(named_result), .source(data));
        expression_result = transform(data);
    end
endmodule
"#,
            "/trace.sv",
        );
        let analysis = host.make_analysis();
        let budget = TraceBudget { max_depth: 2, max_signals: 8, max_assignments: 8 };
        let query = |marker, direction| {
            analysis
                .trace_file_assignments(position(file, &markers, marker), direction, budget)
                .unwrap()
                .unwrap()
        };
        for marker in ["result", "named", "expression"] {
            let trace = query(marker, TraceDirection::Drivers);
            let [assignment] = trace.assignments.as_slice() else { panic!("{marker}: {trace:?}") };
            let kind = if marker == "expression" {
                AssignmentKind::Blocking
            } else {
                AssignmentKind::SubroutineCall
            };
            assert_eq!(assignment.kind, kind);
            assert!(assignment.has_unresolved_operands);
            assert_eq!(trace.signals.iter().filter(|signal| signal.name == "data").count(), 1);
            assert!(trace.signals.iter().any(|signal| signal.name == "config_bit"));
            assert!(
                trace
                    .frontier
                    .iter()
                    .any(|stop| matches!(stop.reason, TraceLimit::SubroutineEffects(_)))
            );
        }
        let loads = query("data", TraceDirection::Loads);
        assert_eq!(
            loads
                .assignments
                .iter()
                .filter(|relation| relation.kind == AssignmentKind::SubroutineCall)
                .count(),
            2
        );
        let formal = query("formal", TraceDirection::Drivers);
        assert_eq!(formal.assignments.len(), 2);
        assert!(formal.assignments.iter().all(|assignment| {
            assignment.kind == AssignmentKind::TaskInput
                && assignment.targets == [formal.root]
                && assignment.value.is_some()
        }));
        let captured = query("config", TraceDirection::Loads);
        assert_eq!(
            captured
                .assignments
                .iter()
                .filter(|relation| relation.kind == AssignmentKind::SubroutineCall)
                .count(),
            2
        );
    }

    #[test]
    fn reports_procedural_overrides_with_their_data_and_source() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic normal, /*marker:stimulus*/stimulus);
    wire /*marker:net*/out;
    logic /*marker:variable*/temporary;
    assign out = normal;
    initial begin
        force out = stimulus;
        #5 release out;
        assign temporary = stimulus;
        #5 deassign temporary;
    end
endmodule
"#,
            "/trace.sv",
        );
        let analysis = host.make_analysis();
        let budget = TraceBudget { max_depth: 2, max_signals: 8, max_assignments: 8 };
        let query = |marker, direction| {
            analysis
                .trace_file_assignments(position(file, &markers, marker), direction, budget)
                .unwrap()
                .unwrap()
        };
        let net = query("net", TraceDirection::Drivers);
        assert_eq!(
            net.assignments.iter().map(|item| item.kind).collect::<Vec<_>>(),
            [AssignmentKind::Continuous, AssignmentKind::Force, AssignmentKind::Release]
        );
        assert_eq!(
            net.frontier
                .iter()
                .filter(|stop| matches!(stop.reason, TraceLimit::ProceduralOverride(_)))
                .count(),
            2
        );
        assert!(net.signals.iter().any(|signal| signal.name == "stimulus"));
        let variable = query("variable", TraceDirection::Drivers);
        assert_eq!(
            variable.assignments.iter().map(|item| item.kind).collect::<Vec<_>>(),
            [AssignmentKind::ProceduralAssign, AssignmentKind::Deassign]
        );
        let loads = query("stimulus", TraceDirection::Loads);
        assert!(loads.assignments.iter().any(|item| item.kind == AssignmentKind::Force));
        assert!(loads.assignments.iter().any(|item| item.kind == AssignmentKind::ProceduralAssign));
    }

    #[test]
    fn traces_testbench_wait_and_delay_operands_without_assuming_execution_time() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb;
    time /*marker:delay*/latency = 5;
    bit /*marker:ready*/ready, stimulus, /*marker:out*/out;
    initial #(latency) wait (ready) out = stimulus;
endmodule
"#,
            "/trace.sv",
        );
        let analysis = host.make_analysis();
        let budget = TraceBudget { max_depth: 1, max_signals: 8, max_assignments: 8 };
        let upstream = analysis
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        let [assignment] = upstream.assignments.as_slice() else {
            panic!("expected one assignment")
        };
        assert!(assignment.has_unresolved_operands);
        assert!(assignment.guards.is_empty());
        for (name, kind) in [
            ("latency", AssignmentInputKind::Control),
            ("ready", AssignmentInputKind::Control),
            ("stimulus", AssignmentInputKind::Data),
        ] {
            let signal = upstream.signals.iter().find(|signal| signal.name == name).unwrap();
            assert!(
                assignment
                    .inputs
                    .iter()
                    .any(|input| input.signal == signal.def && input.kind == kind)
            );
        }
        for marker in ["delay", "ready"] {
            let downstream = analysis
                .trace_file_assignments(
                    position(file, &markers, marker),
                    TraceDirection::Loads,
                    budget,
                )
                .unwrap()
                .unwrap();
            assert!(downstream.assignments.contains(assignment));
        }
    }

    #[test]
    fn lowers_a_packed_write_index_and_indexes_its_read() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic clk, input logic [1:0] /*marker:index*/idx);
    logic [3:0] /*marker:out*/out;
    logic [3:0][1:0] /*marker:matrix*/matrix;
    logic [1:0] /*marker:mem*/mem[0:3];
    logic [7:0] /*marker:lanes*/lanes[0:3];
    wire [7:0] /*marker:word*/word_data = lanes[idx];
    typedef struct packed { logic [7:0] data; logic valid; } packet_t;
    packet_t /*marker:packet*/packet;
    wire [7:0] /*marker:field*/field_data = packet.data;
    always @(posedge clk) out[idx] <= 1'b1;
    always @(posedge clk) matrix[idx] <= 2'b11;
    always @(posedge clk) mem[idx] <= 2'b11;
    always @(posedge clk) lanes[idx][3:0] <= 4'hb;
    always @(posedge clk) lanes[idx][idx +: 2] <= 2'b10;
endmodule
"#,
            "/trace.sv",
        );
        let analysis = host.make_analysis();
        let budget = TraceBudget { max_depth: 1, max_signals: 8, max_assignments: 8 };
        let upstream = analysis
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        let downstream = analysis
            .trace_file_assignments(
                position(file, &markers, "index"),
                TraceDirection::Loads,
                budget,
            )
            .unwrap()
            .unwrap();
        let assignment = &upstream.assignments[0];
        assert_eq!(assignment.target_index, Some(AssignmentValue::Signal(downstream.root)));
        assert!(assignment.value.is_some());
        assert!(downstream.assignments.contains(assignment));
        let matrix = analysis
            .trace_file_assignments(
                position(file, &markers, "matrix"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        assert_eq!(matrix.assignments.len(), 1);
        assert!(matrix.assignments[0].target_index.is_none());
        assert_eq!(matrix.assignments[0].target_element_index, Some(AssignmentValue::Signal(downstream.root)));
        assert!(matrix.assignments[0].value.is_some());
        let memory = analysis
            .trace_file_assignments(
                position(file, &markers, "mem"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        let assignment = &memory.assignments[0];
        assert!(assignment.target_index.is_none());
        assert_eq!(assignment.target_element_index, Some(AssignmentValue::Signal(downstream.root)));
        assert!(assignment.value.is_some());
        let lanes = analysis
            .trace_file_assignments(
                position(file, &markers, "lanes"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        assert_eq!(lanes.assignments.len(), 2);
        for assignment in &lanes.assignments {
            assert_eq!(
                assignment.target_element_index,
                Some(AssignmentValue::Signal(downstream.root)),
            );
            assert!(assignment.value.is_some());
        }
        let lane = lanes.assignments.iter().find(|assignment| assignment.target_range.is_some()).unwrap();
        assert_eq!(lane.target_range, Some([3, 0]));
        assert!(lane.target_index.is_none());
        let indexed = lanes.assignments.iter().find(|assignment| assignment.target_index.is_some()).unwrap();
        assert_eq!(indexed.target_index, Some(AssignmentValue::Signal(downstream.root)));
        assert_eq!(
            indexed.target_indexed_part,
            Some(IndexedPartSelect { width: 2, ascending_indices: true }),
        );
        let word = analysis
            .trace_file_assignments(
                position(file, &markers, "word"),
                TraceDirection::Drivers,
                budget,
            )
            .unwrap()
            .unwrap();
        assert_eq!(
            word.assignments[0].word_read,
            Some((lanes.root, AssignmentValue::Signal(downstream.root))),
        );
        let packet = analysis.trace_file_assignments(
            position(file, &markers, "packet"), TraceDirection::Loads, budget,
        ).unwrap().unwrap();
        let field = analysis.trace_file_assignments(
            position(file, &markers, "field"), TraceDirection::Drivers, budget,
        ).unwrap().unwrap();
        assert_eq!(field.assignments[0].field_read, Some((packet.root, "data".into())));
    }

    #[test]
    fn retains_indexed_part_direction_and_width_in_assignment_traces() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic clk, input logic [2:0] index, input logic [1:0] data);
    logic [0:7] /*marker:ascending*/ascending;
    logic [7:0] /*marker:descending*/descending;
    always @(posedge clk) begin
        ascending[index +: 2] <= data;
        descending[index -: 2] <= ascending[index +: 2];
    end
endmodule
"#,
            "/trace.sv",
        );
        let analysis = host.make_analysis();
        for (name, ascending_indices) in [("ascending", true), ("descending", false)] {
            let trace = analysis.trace_file_assignments(
                position(file, &markers, name),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 1, max_signals: 16, max_assignments: 8 },
            ).unwrap().unwrap();
            let write = trace.assignments.iter().find(|write| write.targets == [trace.root]).unwrap();
            assert_eq!(write.target_indexed_part, Some(IndexedPartSelect { width: 2, ascending_indices }));
            assert!(matches!(write.target_index, Some(AssignmentValue::Signal(_))));
            if name == "descending" {
                assert!(matches!(&write.value, Some(AssignmentValue::IndexedPartSelect(_, _, IndexedPartSelect {
                    width: 2, ascending_indices: true,
                }))));
            }
        }
    }

    #[test]
    fn lowers_four_state_values_and_maps_selected_signals() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic sel, input logic [3:0] grant, input logic signed [3:0] rhs);
    logic [3:0] /*marker:out*/out;
    always_comb
        if (grant[sel] === 1'bx && rhs < 0) out = sel ? {grant[2:1], 2'bxz} : (rhs ^ 4'b1000);
endmodule
"#,
            "/trace.sv",
        );
        let trace = host
            .make_analysis()
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 2, max_signals: 8, max_assignments: 8 },
            )
            .unwrap()
            .unwrap();
        let names = trace
            .signals
            .iter()
            .map(|signal| (signal.def, signal.name.as_str()))
            .collect::<FxHashMap<_, _>>();
        use AssignmentValue::{Binary, BitSelect, Concat, Conditional, Literal, Select, Signal};
        assert_eq!(
            trace.signals.iter().find(|signal| signal.name == "rhs").unwrap().signed,
            Some(true)
        );
        assert_eq!(
            trace.signals.iter().find(|signal| signal.name == "grant").unwrap().signed,
            Some(false)
        );
        let identify = |def| names.get(&def).copied();
        assert_eq!(
            trace.assignments[0].guards[0].expression.clone().unwrap().try_map(&identify),
            Some(GuardExpression::And(
                Box::new(GuardExpression::Value(Binary(
                    ValueBinary::CaseEqual,
                    Box::new(BitSelect("grant", Box::new(Signal("sel")))),
                    Box::new(Literal("x".into(), false)),
                ))),
                Box::new(GuardExpression::Value(Binary(
                    ValueBinary::Less,
                    Box::new(Signal("rhs")),
                    Box::new(AssignmentValue::UnsignedBit(false)),
                ))),
            )),
        );
        assert_eq!(
            trace.assignments[0].value.clone().unwrap().try_map(&identify),
            Some(Conditional(
                Box::new(Signal("sel")),
                Box::new(Concat(vec![Select("grant", 2, 1), Literal("xz".into(), false)])),
                Box::new(Binary(
                    ValueBinary::BitXor,
                    Box::new(Signal("rhs")),
                    Box::new(Literal("1000".into(), false)),
                )),
            )),
        );
    }

    #[test]
    fn indexes_declaration_drivers_and_case_dependencies() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic select, first, second, data);
    wire net = data;
    logic initial_value = 0;
    logic /*marker:target*/out;
    always_comb begin
        case (select)
            first: out = 0;
            second, 1'bx: out = net;
            default: out = initial_value;
        endcase
    end
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let trace = snapshot
            .trace_file_assignments(
                position(file, &markers, "target"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 4, max_signals: 16, max_assignments: 16 },
            )
            .unwrap()
            .unwrap();
        let names = trace
            .signals
            .iter()
            .map(|signal| (signal.def, signal.name.as_str()))
            .collect::<FxHashMap<_, _>>();
        assert_eq!(trace.assignments.len(), 5);
        let process = trace.assignments[0].process.expect("enclosing always process");
        assert!(trace.assignments[..3].iter().all(|relation| relation.process == Some(process)));
        assert!(trace.assignments[3..].iter().all(|relation| relation.process.is_none()));
        let controls = |relation: &AssignmentRelation| {
            relation
                .inputs
                .iter()
                .filter(|input| input.kind == AssignmentInputKind::Control)
                .map(|input| names[&input.signal])
                .collect::<Vec<_>>()
        };
        assert_eq!(controls(&trace.assignments[0]), ["select", "first"]);
        assert_eq!(controls(&trace.assignments[1]), ["select", "first", "second"]);
        assert_eq!(controls(&trace.assignments[2]), ["select", "first", "second"]);
        assert!(trace.assignments[..3].iter().all(|relation| !relation.has_unresolved_operands));
        for (relation, expected) in
            trace.assignments[..3].iter().zip([vec![true], vec![false, true], vec![false, false]])
        {
            assert_eq!(
                relation.guards.iter().map(|guard| guard.taken_when_true).collect::<Vec<_>>(),
                expected,
            );
        }
        assert!(matches!(
            trace.assignments[0].guards[0].expression,
            Some(GuardExpression::Value(AssignmentValue::Binary(ValueBinary::CaseItemEqual, ..)))
        ));
        assert!(matches!(trace.assignments[1].guards[1].expression, Some(GuardExpression::Or(..))));
        assert_eq!(trace.assignments[3].kind, AssignmentKind::Continuous);
        assert_eq!(names[&trace.assignments[3].inputs[0].signal], "data");
        assert_eq!(trace.assignments[4].kind, AssignmentKind::Initialization);
    }

    #[test]
    fn indexes_direct_drivers_and_signal_loads() {
        let (host, file, text, markers) = setup_marked_with_path(
            r#"
module top(input logic clk, rst_n, en, source, other);
    logic next, output_q;
    logic [3:0] /*marker:slice*/sliced;
    assign next = source;
    assign sliced[2:1] = {source, other};
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) output_q <= 0;
        else if (en) /*marker:target*/output_q <= /*marker:dependency*/next;
        else output_q <= other;
    end
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let query =
            |name| snapshot.file_signal_relations(position(file, &markers, name)).unwrap().unwrap();
        let output = query("target");
        assert_eq!(output.drivers.len(), 3);
        assert!(output.loads.is_empty());
        let driver = &output.drivers[1];
        assert_eq!(output.drivers[0].value, Some(AssignmentValue::UnsignedBit(false)));
        assert_eq!(driver.location.file_id, file);
        assert_eq!(&text[driver.location.range], "output_q <= next");
        assert_eq!(driver.kind, AssignmentKind::Nonblocking);
        assert_eq!(driver.targets, vec![output.signal]);
        assert!(!driver.has_unresolved_operands);
        assert_eq!(
            driver
                .guards
                .iter()
                .map(|guard| (&text[guard.location.range], guard.taken_when_true))
                .collect::<Vec<_>>(),
            vec![("!rst_n", false), ("en", true)],
        );
        assert!(matches!(driver.guards[0].expression, Some(GuardExpression::Not(_))));
        assert!(matches!(driver.guards[1].expression, Some(GuardExpression::Signal(_))));
        assert_eq!(
            driver
                .inputs
                .iter()
                .map(|input| (input.kind, &text[input.location.range]))
                .collect::<Vec<_>>(),
            vec![
                (AssignmentInputKind::Data, "next"),
                (AssignmentInputKind::Control, "en"),
                (AssignmentInputKind::Control, "rst_n"),
                (AssignmentInputKind::Trigger(TriggerEdge::Rising), "clk"),
                (AssignmentInputKind::Trigger(TriggerEdge::Falling), "rst_n"),
            ],
        );
        let next = query("dependency");
        assert_eq!(driver.value, Some(AssignmentValue::Signal(next.signal)));
        assert_eq!(next.drivers.len(), 1);
        assert_eq!(next.drivers[0].kind, AssignmentKind::Continuous);
        assert_eq!(next.loads, vec![driver.clone()]);
        let sliced = query("slice");
        assert_eq!(sliced.drivers[0].target_range, Some([2, 1]));
        assert!(matches!(sliced.drivers[0].value, Some(AssignmentValue::Concat(_))));
    }

    #[test]
    fn lowers_case_wildcard_labels_without_losing_four_state_bits() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module tb(input logic [1:0] sel);
    logic /*marker:out*/out;
    always_comb begin
        casez (sel)
            2'b1?: out = 1;
            default: out = 0;
        endcase
    end
endmodule
"#,
            "/case.sv",
        );
        let trace = host
            .make_analysis()
            .trace_file_assignments(
                position(file, &markers, "out"),
                TraceDirection::Drivers,
                TraceBudget { max_depth: 1, max_signals: 8, max_assignments: 8 },
            )
            .unwrap()
            .unwrap();
        let guard = trace.assignments[0].guards[0].expression.clone().unwrap();
        assert!(matches!(
            guard,
            GuardExpression::Value(AssignmentValue::Binary(ValueBinary::CaseItemZ, _, label))
                if *label == AssignmentValue::Literal("1z".into(), false)
        ));
        assert!(!trace.assignments[1].guards[0].taken_when_true);
    }

    #[test]
    fn walks_both_directions_through_cycles_and_reports_budget_limits() {
        let (host, file, _, markers) = setup_marked_with_path(
            r#"
module top(input logic a);
    wire b, c, d;
    assign /*marker:root*/b = a | c;
    assign c = b;
    assign d = c;
endmodule
"#,
            "/trace.sv",
        );
        let snapshot = host.make_analysis();
        let at = position(file, &markers, "root");
        let budget = TraceBudget { max_depth: 8, max_signals: 8, max_assignments: 8 };
        let trace = |direction, budget| {
            snapshot.trace_file_assignments(at, direction, budget).unwrap().unwrap()
        };

        let upstream = trace(TraceDirection::Drivers, budget);
        assert_eq!(upstream.assignments.len(), 2);
        assert!(upstream.frontier.is_empty());
        let downstream = trace(TraceDirection::Loads, budget);
        assert_eq!(downstream.assignments.len(), 3);
        assert!(downstream.frontier.is_empty());

        for (limits, expected) in [
            (TraceBudget { max_depth: 1, ..budget }, TraceLimit::Depth),
            (TraceBudget { max_signals: 2, ..budget }, TraceLimit::Signals),
            (TraceBudget { max_assignments: 1, ..budget }, TraceLimit::Assignments),
        ] {
            let result = trace(TraceDirection::Drivers, limits);
            assert_eq!(result.frontier.len(), 1);
            assert_eq!(result.frontier[0].reason, expected);
        }
    }
}
