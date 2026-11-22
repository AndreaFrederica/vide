use ide::assignment_trace::{
    AssignmentInputKind, AssignmentKind, TraceBudget, TraceDirection, TraceLimit, TriggerEdge,
};

use crate::{
    global_state::snapshot::GlobalStateSnapshot,
    lsp_ext::{
        from_proto,
        lsp_error::LspError,
        to_proto,
        trace::{
            Assignment, Frontier, GenerateBranch, GenerateLabel, Guard,
            HierarchicalReferenceModule, HierarchicalTarget, Input,
            InterfaceArrayAccess, Signal, TRACE_VERSION, TraceCompilation, TraceParams,
            TraceResult,
        },
    },
};

pub(crate) fn handle_trace_drivers(
    snap: GlobalStateSnapshot,
    params: TraceParams,
) -> anyhow::Result<Option<TraceResult>> {
    trace(snap, params, TraceDirection::Drivers)
}

pub(crate) fn handle_trace_loads(
    snap: GlobalStateSnapshot,
    params: TraceParams,
) -> anyhow::Result<Option<TraceResult>> {
    trace(snap, params, TraceDirection::Loads)
}

fn trace(
    snap: GlobalStateSnapshot,
    params: TraceParams,
    direction: TraceDirection,
) -> anyhow::Result<Option<TraceResult>> {
    if !snap.workspace_ready {
        return Err(LspError::new(
            lsp_server::ErrorCode::ContentModified as i32,
            "VIDE is still indexing the trace project".to_owned(),
        )
        .into());
    }
    let position = from_proto::file_position(&snap, params.position)?;
    let budget = TraceBudget {
        max_depth: params.options.max_depth.unwrap_or(32).min(256),
        max_signals: params.options.max_signals.unwrap_or(256).clamp(1, 4096),
        max_assignments: params.options.max_assignments.unwrap_or(512).min(4096),
    };
    let member = params
        .options
        .interface_member
        .as_deref()
        .map(|member| (member, params.options.interface_backing.as_deref()));
    let (root, signals, assignments, frontier, module_truncated) = if let Some(module) =
        &params.options.module
    {
        let Some((signals, assignments, truncated)) =
            snap.analysis.module_assignments(
                position.file_id, module, budget, params.options.hierarchical_only,
            )?
        else {
            return Ok(None);
        };
        (None, signals, assignments, Vec::new(), truncated)
    } else {
        let trace = if !params.options.generic_interfaces.is_empty() {
            let types = params
                .options
                .generic_interfaces
                .into_iter()
                .take(128)
                .map(|site| {
                    Ok::<_, anyhow::Error>((
                        from_proto::file_position(&snap, site.formal)?,
                        from_proto::file_position(&snap, site.interface)?,
                        site.modport,
                    ))
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            snap.analysis.trace_bound_assignments(position, direction, budget, member, &types)?
        } else if member.is_some() {
            snap.analysis.trace_bound_assignments(position, direction, budget, member, &[])?
        } else {
            snap.analysis.trace_file_assignments(position, direction, budget)?
        };
        let Some(trace) = trace else {
            return Ok(None);
        };
        (Some(trace.root), trace.signals, trace.assignments, trace.frontier, false)
    };
    let ids = signals
        .iter()
        .enumerate()
        .map(|(id, signal)| (signal.def, id))
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut reference_modules = match root {
        Some(root) if params.options.include_hierarchical_modules =>
            snap.analysis.hierarchical_reference_modules(root, &signals, direction)?,
        _ => Default::default(),
    };
    let signals = signals
        .into_iter()
        .enumerate()
        .map(|(id, signal)| {
            let (modules, more_modules) = match reference_modules.remove(&signal.def) {
                Some(result) => {
                    let modules = result.modules.into_iter().map(|module| {
                        Ok(HierarchicalReferenceModule {
                            name: module.name,
                            declaration: to_proto::location(&snap, module.declaration)?,
                        })
                    }).collect::<anyhow::Result<_>>()?;
                    (Some(modules), result.truncated)
                }
                _ => (None, false),
            };
            let declaration = signal
                .declaration
                .map(|location| to_proto::location(&snap, location))
                .transpose()?;
            let packed_struct = signal
                .packed_struct
                .map(|location| to_proto::location(&snap, location))
                .transpose()?;
            Ok(Signal {
                id,
                name: signal.name,
                declaration,
                hierarchical_modules: modules,
                has_more_hierarchical_modules: more_modules.then_some(true),
                signed: signal.signed,
                packed_range: signal.packed_range,
                packed_struct,
                lexical_scope: signal.lexical_scope,
                enum_value: signal.enum_value,
                enum_value_unavailable: signal.enum_value_unavailable,
                package_parameter_value: signal.package_parameter_value,
                package_parameter_value_unavailable: signal.package_parameter_value_unavailable,
                instance_parameter: signal.instance_parameter,
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let assignments = assignments
        .into_iter()
        .map(|assignment| {
            let kind = match assignment.kind {
                AssignmentKind::Continuous => "continuous",
                AssignmentKind::Blocking => "blocking",
                AssignmentKind::Nonblocking => "nonblocking",
                AssignmentKind::Initialization => "initialization",
                AssignmentKind::Force => "force",
                AssignmentKind::Release => "release",
                AssignmentKind::ProceduralAssign => "proceduralAssign",
                AssignmentKind::Deassign => "deassign",
                AssignmentKind::SubroutineCall => "subroutineCall",
                AssignmentKind::TaskInput => "taskInput",
            };
            let inputs = assignment
                .inputs
                .into_iter()
                .map(|input| {
                    let (kind, edge) = match input.kind {
                        AssignmentInputKind::Data => ("data", None),
                        AssignmentInputKind::Control => ("control", None),
                        AssignmentInputKind::Trigger(edge) => (
                            "trigger",
                            Some(match edge {
                                TriggerEdge::Rising => "rising",
                                TriggerEdge::Falling => "falling",
                                TriggerEdge::Either => "either",
                                TriggerEdge::Change => "change",
                            }),
                        ),
                    };
                    Ok(Input {
                        signal: ids[&input.signal],
                        kind: kind.into(),
                        edge: edge.map(str::to_owned),
                        location: to_proto::location(&snap, input.location)?,
                        hierarchical: input.hierarchical,
                        hierarchical_path: input.hierarchical_path,
                        hierarchical_indices: input.hierarchical_indices.into_iter()
                            .filter_map(|(segment, expr)| Some((segment, expr.try_map(&|def| ids.get(&def).copied())?)))
                            .collect(),
                        interface_range: input
                            .interface_operand
                            .as_ref()
                            .and_then(|operand| operand.range),
                        interface_component: input
                            .interface_operand
                            .as_ref()
                            .and_then(|operand| operand.component),
                        interface_index: input
                            .interface_operand
                            .as_ref()
                            .and_then(|operand| operand.index_expression.clone())
                            .and_then(|index| index.try_map(&|def| ids.get(&def).copied())),
                        interface_path: input.interface_operand.map(|operand| operand.path),
                        source_offset: input
                            .hierarchical
                            .then(|| input.location.range.start().into()),
                        byte_column: input
                            .hierarchical
                            .then(|| {
                                snap.line_info(input.location.file_id)
                                    .ok()?
                                    .index
                                    .try_line_col(input.location.range.start())
                                    .map(|position| position.col)
                            })
                            .flatten(),
                    })
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            let has_target_index = assignment.target_index.is_some();
            let target_index = assignment
                .target_index
                .and_then(|index| index.try_map(&|def| ids.get(&def).copied()));
            let has_element_index = assignment.target_element_index.is_some();
            let has_target_field = assignment.target_field.is_some();
            let value = assignment
                .value
                .filter(|_| !has_target_index || target_index.is_some())
                .and_then(|value| value.try_map(&|def| ids.get(&def).copied()));
            Ok(Assignment {
                kind: kind.into(),
                location: to_proto::location(&snap, assignment.location)?,
                process: assignment
                    .process
                    .map(|range| to_proto::location(&snap, range))
                    .transpose()?,
                targets: assignment.targets.into_iter().map(|target| ids[&target]).collect(),
                hierarchical_targets: assignment
                    .hierarchical_targets
                    .into_iter()
                    .map(|target| {
                        let location = target.location;
                        Ok(HierarchicalTarget {
                            signal: ids[&target.signal],
                            location: to_proto::location(&snap, location)?,
                            hierarchical_path: target.hierarchical_path,
                            hierarchical_indices: target.hierarchical_indices.into_iter()
                                .filter_map(|(segment, expr)| Some((segment, expr.try_map(&|def| ids.get(&def).copied())?)))
                                .collect(),
                            byte_column: snap
                                .line_info(location.file_id)
                                .ok()
                                .and_then(|info| info.index.try_line_col(location.range.start()))
                                .map(|position| position.col),
                            interface_range: target
                                .interface_operand
                                .as_ref()
                                .and_then(|operand| operand.range),
                            interface_component: target
                                .interface_operand
                                .as_ref()
                                .and_then(|operand| operand.component),
                            interface_index: target
                                .interface_operand
                                .as_ref()
                                .and_then(|operand| operand.index_expression.clone())
                                .and_then(|index| index.try_map(&|def| ids.get(&def).copied())),
                            interface_path: target.interface_operand.map(|operand| operand.path),
                        })
                    })
                    .collect::<anyhow::Result<_>>()?,
                inputs,
                guards: assignment
                    .guards
                    .into_iter()
                    .map(|guard| {
                        Ok(Guard {
                            location: to_proto::location(&snap, guard.location)?,
                            taken_when_true: guard.taken_when_true,
                            expression: guard.expression.and_then(|expression| {
                                expression.try_map(&|def| ids.get(&def).copied())
                            }),
                        })
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?,
                case_entries: assignment
                    .case_entries
                    .into_iter()
                    .map(|entry| Ok(crate::lsp_ext::trace::CaseEntry {
                        selector: to_proto::location(&snap, entry.selector)?,
                        body: to_proto::location(&snap, entry.body)?,
                        default_branch: entry.default_branch,
                    }))
                    .collect::<anyhow::Result<Vec<_>>>()?,
                wait_entries: assignment.wait_entries.into_iter()
                    .map(|entry| to_proto::location(&snap, entry))
                    .collect::<anyhow::Result<Vec<_>>>()?,
                standalone_wait_entries: assignment.standalone_wait_entries.into_iter()
                    .map(|entry| to_proto::location(&snap, entry))
                    .collect::<anyhow::Result<Vec<_>>>()?,
                wait_predicates: assignment
                    .wait_predicates
                    .into_iter()
                    .filter_map(|(location, predicate)| {
                        let expression = predicate.try_map(&|def| ids.get(&def).copied())?;
                        Some(to_proto::location(&snap, location).map(|location| {
                            crate::lsp_ext::trace::WaitPredicate { location, expression }
                        }))
                    })
                    .collect::<anyhow::Result<Vec<_>>>()?,
                generate_branches: assignment
                    .generate_branches
                    .into_iter()
                    .map(|branch| GenerateBranch {
                        loop_scope: branch.loop_scope,
                        loop_variable: branch.loop_variable,
                        lone_if_condition: branch.lone_if_condition,
                        case_without_default: branch.case_without_default,
                        selected: branch.selected.and_then(|site| generate_label(&snap, site)),
                        alternatives: branch
                            .alternatives
                            .into_iter()
                            .filter_map(|site| generate_label(&snap, site))
                            .collect(),
                    })
                    .collect(),
                has_unresolved_operands: assignment.has_unresolved_operands,
                delay_free_continuous: assignment.delay_free_continuous.then_some(true),
                initialization_at_start: assignment.initialization_at_start.then_some(true),
                unresolved_control_only: (assignment.unresolved_control_only && value.is_some())
                    .then_some(true),
                target_range: assignment.target_range,
                value: if has_element_index || has_target_field { None } else { value.clone() },
                word_read: assignment.word_read.and_then(|(signal, index)| {
                    Some(crate::lsp_ext::trace::WordRead {
                        signal: *ids.get(&signal)?,
                        index: index.try_map(&|def| ids.get(&def).copied())?,
                    })
                }),
                field_read: assignment.field_read.and_then(|(signal, field)| {
                    Some(crate::lsp_ext::trace::FieldRead { signal: *ids.get(&signal)?, field })
                }),
                target_field: assignment.target_field.and_then(|(signal, field)| {
                    Some(crate::lsp_ext::trace::FieldRead { signal: *ids.get(&signal)?, field })
                }),
                field_value: if has_target_field { value.clone() } else { None },
                element_value: if has_element_index { value } else { None },
                target_indexed_part: assignment
                    .target_indexed_part
                    .filter(|_| target_index.is_some()),
                target_index,
                target_element_index: assignment
                    .target_element_index
                    .and_then(|index| index.try_map(&|def| ids.get(&def).copied())),
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;

    let frontier = frontier
        .into_iter()
        .map(|frontier| {
            let array = match &frontier.reason {
                TraceLimit::HierarchicalLoad(_, array)
                | TraceLimit::HierarchicalWrite(_, array) => array.as_ref(),
                _ => None,
            };
            let (reason, site) = match frontier.reason {
                TraceLimit::Depth => ("depth", None),
                TraceLimit::Signals => ("signals", None),
                TraceLimit::Assignments => ("assignments", None),
                TraceLimit::HierarchicalLoad(site, _) => ("unresolvedHierarchicalLoad", Some(site)),
                TraceLimit::HierarchicalWrite(site, _) => {
                    ("unresolvedHierarchicalWrite", Some(site))
                }
                TraceLimit::ProceduralOverride(site) => ("proceduralOverride", Some(site)),
                TraceLimit::SubroutineEffects(site) => ("unresolvedSubroutineEffects", Some(site)),
                TraceLimit::RuntimeInput(site) => ("unresolvedRuntimeInput", Some(site)),
                TraceLimit::ProceduralLoop(site) => ("unresolvedProceduralLoop", Some(site)),
                TraceLimit::ProceduralTiming(site) => ("unresolvedProceduralTiming", Some(site)),
                TraceLimit::VirtualInterfaceBinding(site) => {
                    ("unresolvedVirtualInterfaceBinding", Some(site))
                }
                TraceLimit::UpdateEvaluation(site) => ("unresolvedUpdateEvaluation", Some(site)),
            };
            Ok(Frontier {
                signal: ids[&frontier.signal],
                reason: reason.into(),
                location: site.map(|site| to_proto::location(&snap, site)).transpose()?,
                byte_column: site.and_then(|site| {
                    snap.line_info(site.file_id)
                        .ok()?
                        .index
                        .try_line_col(site.range.start())
                        .map(|pos| pos.col)
                }),
                interface_array_access: array
                    .map(|array| {
                        Ok::<_, anyhow::Error>(InterfaceArrayAccess {
                            formal: to_proto::location(&snap, array.formal)?,
                            member_path: array.member_path.clone(),
                        })
                    })
                    .transpose()?,
            })
        })
        .collect::<anyhow::Result<_>>()?;
    let mut diagnostics = vec!["localAssignmentCoverage".into()];
    if assignments.iter().any(|assignment| assignment.has_unresolved_operands) {
        diagnostics.push("unresolvedOperands".into());
    }
    let compilation = if params.options.include_compilation.unwrap_or(false) {
        let plan = snap.analysis.compilation_plan(position.file_id)?;
        let (files, complete) = snap.analysis.trace_compilation_files(position.file_id, &plan)?;
        let urls = |files: &[vfs::FileId]| {
            files.iter().map(|&file| to_proto::url(&snap, file)).collect::<anyhow::Result<Vec<_>>>()
        };
        Some(TraceCompilation {
            roots: urls(plan.primary_roots())?,
            compilation_units: plan
                .compilation_units
                .as_ref()
                .map(|units| {
                    units.iter().map(|unit| urls(unit)).collect::<anyhow::Result<Vec<_>>>()
                })
                .transpose()?,
            compilation_unit_options: plan.compilation_unit_options.as_ref().map(|units| {
                units
                    .iter()
                    .map(|unit| crate::lsp_ext::trace::TraceUnitOptions {
                        include_dirs: unit.include_dir_strings(),
                        defines: unit.predefine_strings(),
                    })
                    .collect()
            }),
            library_files: urls(plan.library_roots())?,
            library_maps: urls(plan.library_maps())?,
            source_libraries: plan
                .source_libraries
                .iter()
                .map(|(file, name)| {
                    Ok(crate::lsp_ext::trace::TraceSourceLibrary {
                        path: to_proto::url(&snap, *file)?,
                        name: name.clone(),
                    })
                })
                .collect::<anyhow::Result<_>>()?,
            files: urls(&files)?,
            include_dirs: plan.include_dirs.iter().map(ToString::to_string).collect(),
            top_modules: plan.top_modules.clone(),
            parameter_overrides: plan.parameter_overrides.clone(),
            default_timescale: plan.default_timescale.clone(),
            defines: plan.predefines.clone(),
            complete,
        })
    } else {
        None
    };
    if module_truncated {
        diagnostics.push("Module assignment limit reached".into());
    }
    Ok(Some(TraceResult {
        schema_version: TRACE_VERSION,
        revision: snap.analysis.snapshot_id().get().to_string(),
        scope: if root.is_some() { "file" } else { "module" }.into(),
        root: root.map_or(0, |root| ids[&root]),
        signals,
        assignments,
        frontier,
        diagnostics,
        compilation,
    }))
}

fn generate_label(
    snap: &GlobalStateSnapshot,
    site: ide::assignment_trace::GenerateLabel,
) -> Option<GenerateLabel> {
    let file = site.source.file_id;
    let lines = snap.line_info(file).ok()?.index;
    let position = lines.try_line_col(site.source.range.start())?;
    let block_end = site.block_end
        .and_then(|offset| lines.try_line_col(offset))
        .map(|end| [end.line, end.col]);
    Some(GenerateLabel {
        name: site.name,
        uri: to_proto::url(snap, file).ok()?,
        line: position.line,
        byte_column: position.col,
        block_end,
        unique_line: site.unique_line.then_some(true),
    })
}
