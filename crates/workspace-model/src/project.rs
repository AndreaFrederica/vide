use triomphe::Arc;
use utils::{line_index::TextRange, paths::AbsPathBuf};

use crate::source_root::SourceRootId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompilationProfileId(pub u32);

// SAFETY: `CompilationProfileId` is a copy-only, `'static` identity value.
unsafe impl salsa::SalsaValue for CompilationProfileId {}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PreprocessConfig {
    pub predefines: Vec<Predefine>,
    pub include_dirs: Vec<AbsPathBuf>,
}

impl PreprocessConfig {
    pub fn with_predefine_strings(
        predefines: impl IntoIterator<Item = impl Into<String>>,
        include_dirs: Vec<AbsPathBuf>,
    ) -> Self {
        Self {
            predefines: predefines.into_iter().map(|predefine| Predefine::new(predefine)).collect(),
            include_dirs,
        }
    }

    pub fn include_dir_strings(&self) -> Vec<String> {
        self.include_dirs.iter().map(ToString::to_string).collect()
    }

    pub fn predefine_strings(&self) -> Vec<String> {
        self.predefines.iter().map(|predefine| predefine.definition.clone()).collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predefine {
    pub definition: String,
    pub source: Option<PredefineSource>,
}

impl Predefine {
    pub fn new(definition: impl Into<String>) -> Self {
        Self { definition: definition.into(), source: None }
    }

    pub fn with_source(definition: impl Into<String>, source: PredefineSource) -> Self {
        Self { definition: definition.into(), source: Some(source) }
    }

    pub fn as_str(&self) -> &str {
        self.definition.as_str()
    }
}

impl From<String> for Predefine {
    fn from(value: String) -> Self {
        Predefine::new(value)
    }
}

impl From<&str> for Predefine {
    fn from(value: &str) -> Self {
        Predefine::new(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredefineSource {
    pub path: AbsPathBuf,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilationProfile {
    pub source_roots: Vec<SourceRootId>,
    pub top_modules: Vec<String>,
    pub preprocess: PreprocessConfig,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExplicitCompilationInputs {
    pub sources: Option<Vec<AbsPathBuf>>,
    pub compilation_units: Option<Vec<Vec<AbsPathBuf>>>,
    pub compilation_unit_options: Option<Vec<PreprocessConfig>>,
    pub library_files: Vec<AbsPathBuf>,
    pub library_maps: Vec<AbsPathBuf>,
    pub source_libraries: Vec<(AbsPathBuf, String)>,
    pub parameter_overrides: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ProjectConfig {
    root_profiles: Vec<Option<CompilationProfileId>>,
    profiles: Vec<CompilationProfile>,
    explicit_inputs: Vec<ExplicitCompilationInputs>,
}

impl ProjectConfig {
    pub fn new(
        root_profiles: Vec<Option<CompilationProfileId>>,
        profiles: Vec<CompilationProfile>,
    ) -> Self {
        Self { root_profiles, profiles, explicit_inputs: Vec::new() }
    }

    pub fn with_explicit_inputs(mut self, explicit_inputs: Vec<ExplicitCompilationInputs>) -> Self {
        self.explicit_inputs = explicit_inputs;
        self
    }

    pub fn explicit_inputs(
        &self,
        profile_id: Option<CompilationProfileId>,
    ) -> Option<&ExplicitCompilationInputs> {
        self.explicit_inputs.get(profile_id?.0 as usize)
    }

    pub fn profile_for_root(&self, root_id: SourceRootId) -> Option<CompilationProfileId> {
        self.root_profiles.get(root_id.0 as usize).copied().flatten()
    }

    pub fn profile(&self, profile_id: CompilationProfileId) -> Option<&CompilationProfile> {
        self.profiles.get(profile_id.0 as usize)
    }

    pub fn root_profile_count(&self) -> usize {
        self.root_profiles.len()
    }

    pub fn has_compilation_profiles(&self) -> bool {
        !self.profiles.is_empty()
    }

    pub fn profile_ids(&self) -> Vec<CompilationProfileId> {
        (0..self.profiles.len())
            .map(|idx| CompilationProfileId(u32::try_from(idx).unwrap_or(u32::MAX)))
            .collect()
    }

    pub fn preprocess_for_profile(
        &self,
        profile_id: Option<CompilationProfileId>,
    ) -> PreprocessConfig {
        profile_id
            .and_then(|profile_id| self.profile(profile_id))
            .map(|profile| profile.preprocess.clone())
            .unwrap_or_default()
    }
}

pub type SharedProjectConfig = Arc<ProjectConfig>;
