use std::sync::LazyLock;

use anyhow::Context;
use const_format::formatcp;
use regex::Regex;
use rustc_hash::FxHashSet;
use serde::Deserialize;
use smol_str::SmolStr;
use toml::Spanned;
use utils::{
    line_index::{TextRange, TextSize},
    paths::{AbsPathBuf, Utf8PathBuf},
};

use crate::macro_def::{MacroAtom, MacroDef, MacroDefSource};
#[cfg(feature = "manifest-schema")]
use crate::project_manifest::MANIFEST_FILE_NAME;

const IDENTIFIER_RE: &str = r"[a-zA-Z_][a-zA-Z0-9$_]*|\\\S* ";
#[cfg(feature = "manifest-schema")]
const MACRO_DEFINITION_SCHEMA_RE: &str = r"^(?:[A-Za-z_][A-Za-z0-9$_]*|\\\S* )(?:=.*)?$";
#[cfg(feature = "manifest-schema")]
pub const TOML_MANIFEST_SCHEMA_VERSION: &str = "v1";
#[cfg(feature = "manifest-schema")]
pub const TOML_MANIFEST_SCHEMA_PATH: &str =
    formatcp!("/schemas/{TOML_MANIFEST_SCHEMA_VERSION}/vide.schema.json");
#[cfg(feature = "manifest-schema")]
pub const TOML_MANIFEST_SCHEMA_URL: &str =
    formatcp!("https://vide.pascal-lab.net{TOML_MANIFEST_SCHEMA_PATH}");

static IDENT_RE: LazyLock<Result<Regex, regex::Error>> =
    LazyLock::new(|| Regex::new(formatcp!("^({IDENTIFIER_RE})$")));
static KV_RE: LazyLock<Result<Regex, regex::Error>> =
    LazyLock::new(|| Regex::new(formatcp!("^({IDENTIFIER_RE})=(.*)$")));

#[derive(Debug, Deserialize)]
#[cfg_attr(feature = "manifest-schema", derive(schemars::JsonSchema))]
#[serde(deny_unknown_fields)]
#[cfg_attr(
    feature = "manifest-schema",
    schemars(
        title = "Vide project manifest",
        description = "Project manifest for the Vide Verilog/SystemVerilog language server.",
        extend("$id" = TOML_MANIFEST_SCHEMA_URL, "x-tombi-table-keys-order" = "schema")
    )
)]
struct TomlManifestSchema {
    /// Top-level module names for the compilation profile.
    #[serde(default)]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "Top-level module names for the compilation profile.",
            extend("examples" = [["top"]])
        )
    )]
    pub top_modules: Vec<String>,
    /// SystemVerilog parameter overrides. Use NAME=value for a top-level parameter or top.instance.NAME=value for an explicit hierarchy path.
    #[serde(default)]
    pub parameter_overrides: Vec<String>,
    /// Default RTL time unit and precision, for example 1ns/1ps.
    #[serde(default)]
    pub default_timescale: Option<String>,
    /// External system subroutines with unverified argument directions.
    #[serde(default)]
    pub external_system_calls: Vec<String>,
    /// Predefined macros. Use NAME or NAME=value strings.
    #[serde(deserialize_with = "de_macros", default)]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "Predefined macros. Use NAME or NAME=value strings.",
            with = "Vec::<String>",
            default = "empty_string_vec",
            inner(regex(pattern = MACRO_DEFINITION_SCHEMA_RE)),
            extend("examples" = [["SYNTHESIS", "DATA_WIDTH=32"]])
        )
    )]
    pub defines: MacroDef,
    /// Workspace-relative shell glob patterns for source files to scan. Omitted
    /// sources scan the workspace root for best-effort indexing without
    /// enabling semantic diagnostics. Use an explicit empty array to
    /// disable workspace indexing.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "Workspace-relative shell glob patterns for source files to scan. Omitted sources scan the workspace root for best-effort indexing without enabling semantic diagnostics. Use an explicit empty array to disable workspace indexing.",
            with = "Vec::<String>",
            extend("examples" = [["rtl/**", "ip/**/*.sv"]])
        )
    )]
    pub sources: Option<Vec<String>>,
    /// Literal compilation inputs in simulator order, relative to this manifest
    /// or absolute.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Option<Vec<String>>"))]
    pub source_files: Option<Vec<Utf8PathBuf>>,
    /// Ordered groups of files parsed together. The groups must partition
    /// source_files.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Option<Vec<Vec<String>>>"))]
    pub compilation_units: Option<Vec<Vec<Utf8PathBuf>>>,
    /// Additional preprocessing options for each entry in compilation_units.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    compilation_unit_options: Option<Vec<TomlCompilationUnitOptions>>,
    /// Explicit Verilog source library files, each parsed in its own
    /// compilation unit.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Vec<String>"))]
    pub library_files: Vec<Utf8PathBuf>,
    /// Library map files containing source mappings or SystemVerilog configs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Vec<String>"))]
    library_maps: Vec<Utf8PathBuf>,
    /// Named Verilog libraries for specific compilation inputs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    source_libraries: Vec<TomlSourceLibrary>,
    /// Include search directories. When omitted and sources is set explicitly,
    /// Vide uses the scan roots inferred from sources. Explicit
    /// include_dirs = [] disables this fallback.
    #[serde(default)]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "Include search directories. When omitted and sources is set explicitly, Vide uses the scan roots inferred from sources. Explicit include_dirs = [] disables this fallback.",
            with = "Vec::<String>",
            default = "empty_string_vec",
            extend("examples" = [["include", "rtl"]])
        )
    )]
    pub include_dirs: Option<Vec<Utf8PathBuf>>,
    /// External library or dependency workspace paths. Paths are resolved
    /// relative to the manifest directory. Each path is loaded as another
    /// workspace: if it contains a project manifest, that manifest is used;
    /// otherwise the path is loaded as an unconfigured library dependency.
    #[serde(default)]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "External library or dependency workspace paths. Paths are resolved relative to the manifest directory. Each path is loaded as another workspace: if it contains a project manifest, that manifest is used; otherwise the path is loaded as an unconfigured library dependency.",
            with = "Vec::<String>",
            default = "empty_string_vec",
            extend("examples" = [["../common_cells"]])
        )
    )]
    pub libraries: Vec<Utf8PathBuf>,
    /// Workspace-relative shell glob patterns to remove from loaded files.
    #[serde(default)]
    #[cfg_attr(
        feature = "manifest-schema",
        schemars(
            description = "Workspace-relative shell glob patterns to remove from loaded files.",
            with = "Vec::<String>",
            default = "empty_string_vec",
            extend("examples" = [["build/**", "sim/work/**", "**/*_bb.v"]])
        )
    )]
    pub exclude: Vec<String>,
}

#[cfg(feature = "manifest-schema")]
fn empty_string_vec() -> Vec<String> {
    Vec::new()
}

#[cfg(feature = "manifest-schema")]
pub fn generated_toml_manifest_schema() -> serde_json::Value {
    let mut schema = serde_json::to_value(schemars::schema_for!(TomlManifestSchema)).unwrap();
    if let Some(root) = schema.as_object_mut() {
        root.insert(
            "x-vide-manifest-names".to_owned(),
            serde_json::json!({
                "primary": MANIFEST_FILE_NAME,
            }),
        );
    }
    schema
}

#[derive(Debug, Deserialize)]
#[cfg_attr(feature = "manifest-schema", derive(schemars::JsonSchema))]
#[serde(deny_unknown_fields)]
struct TomlCompilationUnitOptions {
    #[serde(default, deserialize_with = "de_macros")]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Vec<String>"))]
    defines: MacroDef,
    #[serde(default)]
    #[cfg_attr(feature = "manifest-schema", schemars(with = "Vec<String>"))]
    include_dirs: Vec<Utf8PathBuf>,
}

#[derive(Debug, Deserialize)]
#[cfg_attr(feature = "manifest-schema", derive(schemars::JsonSchema))]
#[serde(deny_unknown_fields)]
struct TomlSourceLibrary {
    #[cfg_attr(feature = "manifest-schema", schemars(with = "String"))]
    path: Utf8PathBuf,
    name: String,
}

fn de_macros<'de, D>(deserializer: D) -> Result<MacroDef, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let res = Vec::<Spanned<SmolStr>>::deserialize(deserializer)?;
    let ident_re = IDENT_RE.as_ref().map_err(|err| {
        serde::de::Error::custom(format!("invalid macro identifier regex: {err}"))
    })?;
    let kv_re = KV_RE
        .as_ref()
        .map_err(|err| serde::de::Error::custom(format!("invalid macro key-value regex: {err}")))?;
    let mut macros = FxHashSet::default();
    let mut sources = Vec::new();
    for macr in res {
        let range = spanned_text_range(macr.span()).map_err(serde::de::Error::custom)?;
        let macr = macr.into_inner();
        let atom = if ident_re.is_match(&macr) {
            Ok(MacroAtom::Flag(macr))
        } else if let Some(caps) = kv_re.captures(&macr) {
            let Some(key_match) = caps.get(1) else {
                return Err(serde::de::Error::custom(format!("Invalid macro definition: {macr}")));
            };
            let Some(value_match) = caps.get(2) else {
                return Err(serde::de::Error::custom(format!("Invalid macro definition: {macr}")));
            };
            let mut key: SmolStr = key_match.as_str().into();
            let value = value_match.as_str().into();
            if key.starts_with('\\') {
                let Some(stripped) = key.strip_prefix('\\').and_then(|key| key.strip_suffix(' '))
                else {
                    return Err(serde::de::Error::custom(format!(
                        "Invalid escaped macro name: {macr}"
                    )));
                };
                key = stripped.into();
            }
            Ok(MacroAtom::KeyValue { key, value })
        } else {
            Err(serde::de::Error::custom(format!("Invalid macro definition: {macr}")))
        }?;
        macros.insert(atom.clone());
        sources.push(MacroDefSource { atom, range });
    }
    Ok(MacroDef { macros, sources })
}

fn normalize_timescale(value: &str) -> anyhow::Result<String> {
    static SCALE: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(r"^(1|10|100) *(s|ms|us|ns|ps|fs) */ *(1|10|100) *(s|ms|us|ns|ps|fs)$")
            .expect("valid timescale grammar")
    });
    let captures = SCALE
        .captures(value.trim())
        .with_context(|| format!("Invalid default_timescale {value:?}"))?;
    let exponent = |magnitude: &str, unit: &str| {
        let units = ["s", "ms", "us", "ns", "ps", "fs"];
        let index = units.iter().position(|candidate| *candidate == unit).unwrap();
        magnitude.len() as i32 - 3 * index as i32
    };
    anyhow::ensure!(
        exponent(&captures[3], &captures[4]) <= exponent(&captures[1], &captures[2]),
        "Default timescale precision exceeds the time unit in {value:?}",
    );
    Ok(format!("{}{}/{}{}", &captures[1], &captures[2], &captures[3], &captures[4]))
}

fn spanned_text_range(span: std::ops::Range<usize>) -> Result<TextRange, String> {
    let start = u32::try_from(span.start)
        .map_err(|_| format!("manifest range start is too large: {}", span.start))?;
    let end = u32::try_from(span.end)
        .map_err(|_| format!("manifest range end is too large: {}", span.end))?;
    Ok(TextRange::new(TextSize::from(start), TextSize::from(end)))
}

#[derive(Debug, PartialEq, Eq)]
pub struct TomlWorkspace {
    pub manifest_path: AbsPathBuf,
    pub top_modules: Vec<String>,
    pub parameter_overrides: Vec<String>,
    pub default_timescale: Option<String>,
    pub external_system_calls: Vec<String>,
    pub workspace_root: AbsPathBuf,
    pub macro_defs: MacroDef,
    pub source_patterns: Option<Vec<String>>,
    pub source_files: Option<Vec<AbsPathBuf>>,
    pub compilation_units: Option<Vec<Vec<AbsPathBuf>>>,
    pub compilation_unit_options: Option<Vec<workspace_model::PreprocessConfig>>,
    pub library_files: Vec<AbsPathBuf>,
    pub library_maps: Vec<AbsPathBuf>,
    pub source_libraries: Vec<(AbsPathBuf, String)>,
    pub include_dirs: Option<Vec<AbsPathBuf>>,
    pub libraries: Vec<AbsPathBuf>,
    pub exclude_patterns: Vec<String>,
}

impl TomlWorkspace {
    pub fn load_from_file(toml: &AbsPathBuf) -> anyhow::Result<Self> {
        let toml_file =
            std::fs::read_to_string(toml).with_context(|| format!("failed to read {:?}", toml))?;

        let toml_schema: TomlManifestSchema =
            toml::from_str(&toml_file).with_context(|| format!("failed to parse {:?}", toml))?;

        let top_modules = toml_schema.top_modules;
        let parameter_overrides = toml_schema.parameter_overrides;
        for parameter in &parameter_overrides {
            anyhow::ensure!(
                parameter.split_once('=').is_some_and(
                    |(name, value)| !name.trim().is_empty() && !value.trim().is_empty()
                ),
                "Invalid parameter override {parameter:?}"
            );
        }
        let default_timescale =
            toml_schema.default_timescale.as_deref().map(normalize_timescale).transpose()?;
        let mut external_system_calls = toml_schema.external_system_calls;
        anyhow::ensure!(external_system_calls.len() <= 16384, "Too many external system calls");
        external_system_calls.sort_unstable();
        external_system_calls.dedup();
        let workspace_root = toml
            .parent()
            .with_context(|| format!("manifest path has no parent: {toml}"))?
            .to_path_buf();
        let macro_defs = toml_schema.defines;

        let include_dirs = toml_schema.include_dirs.map(|paths| {
            paths.into_iter().map(|path| workspace_root.absolutize(path)).collect::<Vec<_>>()
        });
        let source_patterns = toml_schema.sources;
        let source_files = toml_schema.source_files.map(|paths| {
            paths.into_iter().map(|path| workspace_root.absolutize(path)).collect::<Vec<_>>()
        });
        anyhow::ensure!(
            source_patterns.is_none() || source_files.is_none(),
            "sources and source_files are mutually exclusive"
        );
        let compilation_units = toml_schema.compilation_units.map(|units| {
            units
                .into_iter()
                .map(|unit| {
                    unit.into_iter().map(|path| workspace_root.absolutize(path)).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        });
        if let Some(units) = &compilation_units {
            anyhow::ensure!(
                units.iter().all(|unit| !unit.is_empty())
                    && source_files.as_ref().is_some_and(|files| {
                        units.iter().flatten().eq(files)
                            && files.iter().collect::<std::collections::HashSet<_>>().len()
                                == files.len()
                    }),
                "compilation_units must partition source_files in order, with each source listed once"
            );
        }
        let compilation_unit_options = toml_schema.compilation_unit_options.map(|options| {
            options
                .into_iter()
                .map(|unit| workspace_model::PreprocessConfig {
                    predefines: unit.defines.to_ordered_predefines(toml),
                    include_dirs: unit
                        .include_dirs
                        .into_iter()
                        .map(|path| workspace_root.absolutize(path))
                        .collect(),
                })
                .collect::<Vec<_>>()
        });
        if let Some(options) = &compilation_unit_options {
            anyhow::ensure!(
                compilation_units.as_ref().is_some_and(|units| units.len() == options.len()),
                "compilation_unit_options must have one entry per compilation unit"
            );
        }
        let library_files = toml_schema
            .library_files
            .into_iter()
            .map(|path| workspace_root.absolutize(path))
            .collect::<Vec<_>>();
        let library_maps = toml_schema
            .library_maps
            .into_iter()
            .map(|path| workspace_root.absolutize(path))
            .collect::<Vec<_>>();
        let source_libraries = toml_schema
            .source_libraries
            .into_iter()
            .map(|entry| (workspace_root.absolutize(entry.path), entry.name))
            .collect::<Vec<_>>();
        if !source_libraries.is_empty() {
            let source_paths = source_files
                .iter()
                .flatten()
                .chain(&library_files)
                .collect::<std::collections::HashSet<_>>();
            let mut names = std::collections::HashMap::new();
            for (path, name) in &source_libraries {
                anyhow::ensure!(
                    source_paths.contains(path)
                        && !name.trim().is_empty()
                        && names.insert(path, name.as_str()).is_none(),
                    "source_libraries must name each explicit source at most once: {path}"
                );
            }
            for unit in compilation_units.iter().flatten() {
                let mut libraries =
                    unit.iter().map(|path| names.get(path).copied().unwrap_or("work"));
                if let Some(first) = libraries.next() {
                    anyhow::ensure!(
                        libraries.all(|library| library == first),
                        "Each compilation unit must belong to one source library"
                    );
                }
            }
        }
        let libraries = toml_schema
            .libraries
            .into_iter()
            .map(|path| workspace_root.absolutize(path))
            .collect::<Vec<_>>();
        let exclude_patterns = toml_schema.exclude;

        Ok(TomlWorkspace {
            manifest_path: toml.clone(),
            top_modules,
            parameter_overrides,
            default_timescale,
            external_system_calls,
            workspace_root,
            macro_defs,
            source_patterns,
            source_files,
            compilation_units,
            compilation_unit_options,
            library_files,
            library_maps,
            source_libraries,
            include_dirs,
            libraries,
            exclude_patterns,
        })
    }
}

#[cfg(test)]
mod tests {
    use utils::test_support::TestDir;

    use super::*;

    #[test]
    fn test_de_macros() {
        let toml = r#"
top_modules = ["main"]
defines = [
    "foo",
    "bar",
    "FOO=bar",
    "BAR=foo",
    "BAZ=foo bar",
    "eqwe=123",
]
        "#;
        let toml_schema: TomlManifestSchema = toml::from_str(toml).unwrap();
        assert_eq!(toml_schema.top_modules, ["main"]);
        let mut macros = FxHashSet::default();
        macros.insert(MacroAtom::Flag("foo".into()));
        macros.insert(MacroAtom::Flag("bar".into()));
        macros.insert(MacroAtom::KeyValue { key: "FOO".into(), value: "bar".into() });
        macros.insert(MacroAtom::KeyValue { key: "BAR".into(), value: "foo".into() });
        macros.insert(MacroAtom::KeyValue { key: "BAZ".into(), value: "foo bar".into() });
        macros.insert(MacroAtom::KeyValue { key: "eqwe".into(), value: "123".into() });
        assert_eq!(toml_schema.defines.macros, macros);
        assert_eq!(toml_schema.defines.sources.len(), 6);
        assert_eq!(
            toml_schema.defines.sources[0],
            MacroDefSource {
                atom: MacroAtom::Flag("foo".into()),
                range: range_of(toml, "\"foo\"")
            }
        );
        assert_eq!(
            toml_schema.defines.sources[2],
            MacroDefSource {
                atom: MacroAtom::KeyValue { key: "FOO".into(), value: "bar".into() },
                range: range_of(toml, "\"FOO=bar\"")
            }
        );
    }

    #[test]
    fn macro_predefines_are_stable() {
        let toml = r#"
defines = [
    "BAR=foo",
    "FOO",
]
        "#;
        let toml_schema: TomlManifestSchema = toml::from_str(toml).unwrap();
        assert_eq!(toml_schema.defines.to_predefine_strings(), ["BAR=foo", "FOO"]);
    }

    #[test]
    fn macro_predefines_keep_manifest_source_ranges() {
        let root = TestDir::new("manifest-predefine-ranges");
        let manifest_text = r#"
defines = [
    "BAR=foo",
    "FOO",
]
"#;
        let manifest = root.write("vide.toml", manifest_text);

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();
        let predefines = workspace.macro_defs.to_predefines(Some(&workspace.manifest_path));

        let foo = predefines
            .iter()
            .find(|predefine| predefine.definition == "FOO")
            .expect("FOO predefine expected");
        let source = foo.source.as_ref().expect("FOO should carry manifest source");
        assert_eq!(source.path, manifest);
        assert_eq!(source.range, range_of(manifest_text, "\"FOO\""));
    }

    #[test]
    fn empty_manifest_omits_source_patterns() {
        let root = TestDir::new("empty-manifest");
        let manifest = root.write("vide.toml", "");

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();

        assert_eq!(workspace.source_patterns, None);
        assert_eq!(workspace.include_dirs, None);
        assert!(workspace.libraries.is_empty());
        assert!(workspace.exclude_patterns.is_empty());
    }

    #[test]
    fn configured_empty_sources_do_not_default_to_workspace_root() {
        let root = TestDir::new("empty-sources");
        let manifest = root.write("vide.toml", "sources = []\n");

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();

        assert_eq!(workspace.source_patterns, Some(Vec::new()));
    }

    #[test]
    fn keeps_source_and_exclude_globs_relative_to_workspace() {
        let root = TestDir::new("manifest-source-exclude-globs");
        root.create_dir_all("rtl");
        let manifest = root.write(
            "vide.toml",
            "sources = [\"rtl/**\"]\nexclude = [\"build/**\", \"**/*_bb.v\"]\n",
        );

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();

        assert_eq!(workspace.source_patterns, Some(vec!["rtl/**".to_owned()]));
        assert_eq!(workspace.exclude_patterns, ["build/**", "**/*_bb.v"]);
    }

    #[test]
    fn configured_empty_include_dirs_do_not_default_to_sources() {
        let root = TestDir::new("empty-include-dirs");
        root.create_dir_all("rtl");
        let manifest = root.write("vide.toml", "sources = [\"rtl/**\"]\ninclude_dirs = []\n");

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();

        assert_eq!(workspace.include_dirs, Some(Vec::new()));
    }

    #[test]
    fn parses_paths_as_absolute_paths() {
        let root = TestDir::new("manifest-paths");
        let manifest = root.write(
            "vide.toml",
            r#"include_dirs = ["include"]
libraries = ["../pkg"]
"#,
        );

        let workspace = TomlWorkspace::load_from_file(&manifest).unwrap();

        assert_eq!(workspace.include_dirs, Some(vec![root.join("include")]));
        assert_eq!(workspace.libraries, [root.join("../pkg")]);
    }

    fn range_of(text: &str, needle: &str) -> TextRange {
        let start = text.find(needle).expect("needle should exist in fixture");
        TextRange::new(
            TextSize::from(u32::try_from(start).unwrap()),
            TextSize::from(u32::try_from(start + needle.len()).unwrap()),
        )
    }
}
