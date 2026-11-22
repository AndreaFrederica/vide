use lsp_types::{Location, TextDocumentPositionParams, request::Request};
use serde::{Deserialize, Serialize};

pub(crate) const TRACE_VERSION: u32 = 1;

pub(crate) enum TraceDrivers {}
pub(crate) enum TraceLoads {}

impl Request for TraceDrivers {
    type Params = TraceParams;
    type Result = Option<TraceResult>;

    const METHOD: &'static str = "vide/traceDrivers";
}

impl Request for TraceLoads {
    type Params = TraceParams;
    type Result = Option<TraceResult>;

    const METHOD: &'static str = "vide/traceLoads";
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceParams {
    #[serde(flatten)]
    pub position: TextDocumentPositionParams,
    #[serde(default)]
    pub options: TraceOptions,
}

#[derive(Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceOptions {
    pub module: Option<String>,
    #[serde(default)]
    pub hierarchical_only: bool,
    #[serde(default)]
    pub include_hierarchical_modules: bool,
    pub max_depth: Option<usize>,
    pub max_signals: Option<usize>,
    pub max_assignments: Option<usize>,
    pub include_compilation: Option<bool>,
    pub interface_member: Option<String>,
    pub interface_backing: Option<String>,
    #[serde(default)]
    pub generic_interfaces: Vec<GenericInterfaceBinding>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct GenericInterfaceBinding {
    pub formal: TextDocumentPositionParams,
    pub interface: TextDocumentPositionParams,
    #[serde(default)]
    pub modport: Option<String>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceResult {
    pub schema_version: u32,
    pub revision: String,
    pub scope: String,
    pub root: usize,
    pub signals: Vec<Signal>,
    pub assignments: Vec<Assignment>,
    pub frontier: Vec<Frontier>,
    pub diagnostics: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compilation: Option<TraceCompilation>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceCompilation {
    pub roots: Vec<lsp_types::Url>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compilation_units: Option<Vec<Vec<lsp_types::Url>>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compilation_unit_options: Option<Vec<TraceUnitOptions>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub library_files: Vec<lsp_types::Url>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub library_maps: Vec<lsp_types::Url>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_libraries: Vec<TraceSourceLibrary>,
    pub files: Vec<lsp_types::Url>,
    pub include_dirs: Vec<String>,
    pub top_modules: Vec<String>,
    pub parameter_overrides: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub default_timescale: Option<String>,
    pub defines: Vec<String>,
    pub complete: bool,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceUnitOptions {
    pub include_dirs: Vec<String>,
    pub defines: Vec<String>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct TraceSourceLibrary {
    pub path: lsp_types::Url,
    pub name: String,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct Signal {
    pub id: usize,
    pub name: String,
    pub declaration: Option<Location>,
    #[serde(rename = "hierarchicalModules", default, skip_serializing_if = "Option::is_none")]
    pub hierarchical_modules: Option<Vec<HierarchicalReferenceModule>>,
    #[serde(rename = "hasMoreHierarchicalModules", default, skip_serializing_if = "Option::is_none")]
    pub has_more_hierarchical_modules: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signed: Option<bool>,
    #[serde(rename = "packedRange", default, skip_serializing_if = "Option::is_none")]
    pub packed_range: Option<[i32; 2]>,
    #[serde(rename = "packedStruct", skip_serializing_if = "Option::is_none")]
    pub packed_struct: Option<Location>,
    #[serde(rename = "lexicalScope", default, skip_serializing_if = "Vec::is_empty")]
    pub lexical_scope: Vec<String>,
    #[serde(rename = "enumValue", default, skip_serializing_if = "Option::is_none")]
    pub enum_value: Option<ide::assignment_trace::TraceEnumValue>,
    #[serde(rename = "enumValueUnavailable", default, skip_serializing_if = "Option::is_none")]
    pub enum_value_unavailable: Option<bool>,
    #[serde(rename = "packageParameterValue", default, skip_serializing_if = "Option::is_none")]
    pub package_parameter_value: Option<ide::assignment_trace::TraceEnumValue>,
    #[serde(
        rename = "packageParameterValueUnavailable",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub package_parameter_value_unavailable: Option<bool>,
    #[serde(rename = "instanceParameter", default, skip_serializing_if = "Option::is_none")]
    pub instance_parameter: Option<bool>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct HierarchicalReferenceModule {
    pub name: String,
    pub declaration: Location,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Assignment {
    pub kind: String,
    pub location: Location,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub process: Option<Location>,
    pub targets: Vec<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub hierarchical_targets: Vec<HierarchicalTarget>,
    pub inputs: Vec<Input>,
    pub guards: Vec<Guard>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub case_entries: Vec<CaseEntry>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub wait_entries: Vec<Location>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub standalone_wait_entries: Vec<Location>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub wait_predicates: Vec<WaitPredicate>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub generate_branches: Vec<GenerateBranch>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub word_read: Option<WordRead>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub field_read: Option<FieldRead>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_field: Option<FieldRead>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub field_value: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_range: Option<[i32; 2]>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_index: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_element_index: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub element_value: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_indexed_part: Option<ide::assignment_trace::IndexedPartSelect>,
    pub has_unresolved_operands: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub delay_free_continuous: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initialization_at_start: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unresolved_control_only: Option<bool>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WordRead {
    pub signal: usize,
    pub index: ide::assignment_trace::AssignmentValue<usize>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct FieldRead {
    pub signal: usize,
    pub field: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct HierarchicalTarget {
    pub signal: usize,
    pub location: Location,
    pub byte_column: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hierarchical_path: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub hierarchical_indices: Vec<(usize, ide::assignment_trace::AssignmentValue<usize>)>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interface_index: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_range: Option<[i32; 2]>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_component: Option<[u32; 2]>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct GenerateLabel {
    pub name: String,
    pub uri: lsp_types::Url,
    pub line: u32,
    pub byte_column: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub block_end: Option<[u32; 2]>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unique_line: Option<bool>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct GenerateBranch {
    pub selected: Option<GenerateLabel>,
    pub alternatives: Vec<GenerateLabel>,
    #[serde(rename = "loopScope", default)]
    pub loop_scope: bool,
    #[serde(rename = "loopVariable", default, skip_serializing_if = "Option::is_none")]
    pub loop_variable: Option<String>,
    #[serde(rename = "loneIfCondition", default, skip_serializing_if = "Option::is_none")]
    pub lone_if_condition: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(rename = "caseWithoutDefault", default, skip_serializing_if = "Option::is_none")]
    pub case_without_default: Option<ide::assignment_trace::GenerateCaseMatch>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Guard {
    pub location: Location,
    pub taken_when_true: bool,
    pub expression: Option<ide::assignment_trace::GuardExpression<usize>>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WaitPredicate {
    pub location: Location,
    pub expression: ide::assignment_trace::GuardExpression<usize>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CaseEntry {
    pub selector: Location,
    pub body: Location,
    pub default_branch: bool,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Input {
    pub signal: usize,
    pub kind: String,
    pub edge: Option<String>,
    pub location: Location,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub hierarchical: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hierarchical_path: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub hierarchical_indices: Vec<(usize, ide::assignment_trace::AssignmentValue<usize>)>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_column: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_offset: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interface_index: Option<ide::assignment_trace::AssignmentValue<usize>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_range: Option<[i32; 2]>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub interface_component: Option<[u32; 2]>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Frontier {
    pub signal: usize,
    pub reason: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<Location>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub byte_column: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interface_array_access: Option<InterfaceArrayAccess>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InterfaceArrayAccess {
    pub formal: Location,
    pub member_path: String,
}
