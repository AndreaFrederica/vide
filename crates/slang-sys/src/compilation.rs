mod ffi;

use std::pin::Pin;

use cxx::UniquePtr;

use crate::{
    diagnostic::SyntaxDiagnostic,
    syntax::{SyntaxTree, SyntaxTreeBuffer, SyntaxTreeOptions},
};

pub struct Compilation {
    raw: UniquePtr<ffi::Compilation>,
}

impl Default for Compilation {
    fn default() -> Self {
        Self::new()
    }
}

impl Compilation {
    pub fn new() -> Self {
        Self::new_with_options(&[], &[])
    }

    pub fn new_with_top_modules(top_modules: &[String]) -> Self {
        Self::new_with_options(top_modules, &[])
    }

    pub fn new_with_options(top_modules: &[String], parameter_overrides: &[String]) -> Self {
        Self { raw: ffi::new_compilation(top_modules.to_vec(), parameter_overrides.to_vec()) }
    }

    pub fn add_syntax_tree(&mut self, tree: &SyntaxTree) {
        ffi::add_syntax_tree(self.raw_pin(), tree.raw.clone());
    }

    pub fn register_source_buffers(&mut self, buffers: &[SyntaxTreeBuffer]) {
        self.register_source_buffers_with_libraries(buffers, |_| String::new());
    }

    pub fn register_source_buffers_with_libraries(
        &mut self,
        buffers: &[SyntaxTreeBuffer],
        library_for: impl Fn(&str) -> String,
    ) {
        ffi::register_source_buffers(
            self.raw_pin(),
            buffers.iter().map(|buffer| buffer.path.clone()).collect(),
            buffers.iter().map(|buffer| buffer.text.clone()).collect(),
            buffers.iter().map(|buffer| library_for(&buffer.path)).collect(),
        );
    }

    pub fn parse_syntax_tree_from_text(
        &mut self,
        text: &str,
        name: &str,
        path: &str,
        options: &SyntaxTreeOptions,
    ) -> SyntaxTree {
        let raw_options = self.raw_parse_options(options);
        SyntaxTree::from_raw(ffi::parse_syntax_tree_from_text(
            self.raw_pin(),
            text,
            name,
            path,
            raw_options,
        ))
    }

    pub fn parse_syntax_tree_from_buffer(
        &mut self,
        name: &str,
        path: &str,
        options: &SyntaxTreeOptions,
        library_unit: bool,
    ) -> SyntaxTree {
        if !options.include_buffers.is_empty() {
            panic!("buffer parsing requires source buffers to be registered on the compilation");
        }
        let raw_options = self.raw_parse_options(options);
        SyntaxTree::from_raw(ffi::parse_syntax_tree_from_buffer(
            self.raw_pin(),
            name,
            path,
            raw_options,
            library_unit,
        ))
    }

    pub fn parse_grouped_sources(
        &mut self,
        paths: Vec<String>,
        options: &SyntaxTreeOptions,
    ) -> SyntaxTree {
        SyntaxTree::from_raw(ffi::parse_grouped_sources(
            self.raw_pin(),
            paths,
            options.predefines.clone(),
            options.include_paths.clone(),
        ))
    }

    pub fn project_source_file(group: &SyntaxTree, path: &str) -> SyntaxTree {
        SyntaxTree::from_raw(ffi::project_source_file(group.raw.as_ref().unwrap(), path))
    }

    pub fn parse_library_map_syntax_tree_from_text(
        &mut self,
        text: &str,
        name: &str,
        path: &str,
    ) -> SyntaxTree {
        SyntaxTree::from_raw(ffi::parse_library_map_syntax_tree_from_text(
            self.raw_pin(),
            text,
            name,
            path,
        ))
    }

    pub fn parse_library_map_syntax_tree_from_buffer(
        &mut self,
        name: &str,
        path: &str,
        options: &SyntaxTreeOptions,
    ) -> SyntaxTree {
        if !options.include_buffers.is_empty()
            || !options.predefines.is_empty()
            || !options.include_paths.is_empty()
            || !options.expand_includes
        {
            panic!("library map buffer parsing received unsupported syntax options");
        }
        SyntaxTree::from_raw(ffi::parse_library_map_syntax_tree_from_buffer(
            self.raw_pin(),
            name,
            path,
            options.collect_expected_syntax,
            options.expected_syntax_offset.unwrap_or_default(),
            options.expected_syntax_offset.is_some(),
        ))
    }

    pub fn parse_diagnostics_with_options(
        &self,
        warning_options: &[String],
    ) -> Vec<SyntaxDiagnostic> {
        ffi::parse_diagnostics(&self.raw, warning_options.to_vec())
            .into_iter()
            .map(SyntaxDiagnostic::from_raw)
            .collect()
    }

    pub fn semantic_diagnostics_with_options(
        &self,
        warning_options: &[String],
    ) -> Vec<SyntaxDiagnostic> {
        ffi::semantic_diagnostics(&self.raw, warning_options.to_vec())
            .into_iter()
            .map(SyntaxDiagnostic::from_raw)
            .collect()
    }

    fn raw_pin(&mut self) -> Pin<&mut ffi::Compilation> {
        self.raw.as_mut().expect("Slang compilation unexpectedly null")
    }

    fn raw_parse_options(&self, options: &SyntaxTreeOptions) -> ffi::ParseSyntaxTreeOptions {
        ffi::ParseSyntaxTreeOptions {
            predefines: options.predefines.clone(),
            include_paths: options.include_paths.clone(),
            include_buffer_paths: options
                .include_buffers
                .iter()
                .map(|buffer| buffer.path.clone())
                .collect(),
            include_buffer_texts: options
                .include_buffers
                .iter()
                .map(|buffer| buffer.text.clone())
                .collect(),
            expand_includes: options.expand_includes,
            collect_expected_syntax: options.collect_expected_syntax,
            expected_syntax_offset: options.expected_syntax_offset.unwrap_or_default(),
            has_expected_syntax_offset: options.expected_syntax_offset.is_some(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{SyntaxKind, SyntaxTreeBuffer};

    #[test]
    fn adding_a_cloned_tree_does_not_invalidate_the_original() {
        let mut parser = Compilation::new();
        let tree = parser.parse_syntax_tree_from_text(
            "module demo; endmodule",
            "source",
            "source.sv",
            &SyntaxTreeOptions::default(),
        );
        let original = tree.clone();

        let mut compilation = Compilation::new();
        compilation.add_syntax_tree(&tree);

        assert_eq!(original.root().kind(), SyntaxKind::COMPILATION_UNIT);
    }

    #[test]
    fn compilation_keeps_an_attached_tree_source_session_alive() {
        let tree =
            SyntaxTree::from_file_in_memory("module demo; endmodule\n", "source", "source.sv");
        let mut compilation = Compilation::new();
        compilation.add_syntax_tree(&tree);
        drop(tree);

        assert!(compilation.parse_diagnostics_with_options(&[]).is_empty());
    }

    #[test]
    fn empty_compilation_has_no_diagnostics() {
        let compilation = Compilation::new();

        assert!(compilation.parse_diagnostics_with_options(&[]).is_empty());
        assert!(compilation.semantic_diagnostics_with_options(&[]).is_empty());
    }

    #[test]
    fn top_parameter_overrides_select_the_elaborated_branch() {
        let tree = SyntaxTree::from_file_in_memory(
            "module top #(parameter bit Mode = 0); if (Mode) begin $error(\"override branch\"); end endmodule",
            "top",
            "top.sv",
        );
        let top = ["top".to_owned()];
        let mut default = Compilation::new_with_options(&top, &[]);
        default.add_syntax_tree(&tree);
        let has_marker = |diagnostics: &[SyntaxDiagnostic]| {
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains("override branch")
                    || diagnostic.args.iter().any(|arg| arg.contains("override branch"))
            })
        };
        assert!(!has_marker(&default.semantic_diagnostics_with_options(&[])));

        let mut overridden = Compilation::new_with_options(&top, &["Mode=1".to_owned()]);
        overridden.add_syntax_tree(&tree);
        let diagnostics = overridden.semantic_diagnostics_with_options(&[]);
        assert!(has_marker(&diagnostics), "{diagnostics:?}");
    }

    #[test]
    fn qualified_overrides_select_only_the_named_top_and_instance() {
        let tree = SyntaxTree::from_file_in_memory(
            r#"
module child #(parameter bit Mode = 0);
    if (Mode) begin : selected $error("selected child"); end
    else begin : unchanged $error("default child"); end
endmodule
module top_a #(parameter bit Mode = 0);
    if (Mode) begin : selected $error("selected top_a"); end
    child dut();
    child sibling();
endmodule
module top_b #(parameter bit Mode = 0);
    if (Mode) begin : selected $error("selected top_b"); end
endmodule
"#,
            "scoped",
            "scoped.sv",
        );
        let tops = ["top_a".to_owned(), "top_b".to_owned()];
        let overrides = ["top_a.Mode=1".to_owned(), "top_a.dut.Mode=1".to_owned()];
        let mut compilation = Compilation::new_with_options(&tops, &overrides);
        compilation.add_syntax_tree(&tree);
        let diagnostics = compilation.semantic_diagnostics_with_options(&[]);
        let marked = |marker: &str| {
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains(marker)
                    || diagnostic.args.iter().any(|arg| arg.contains(marker))
            })
        };
        assert!(
            marked("selected top_a")
                && !marked("selected top_b")
                && marked("selected child")
                && marked("default child"),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn indexed_overrides_elaborate_instance_arrays_and_negative_generate_indices() {
        let tree = SyntaxTree::from_file_in_memory(
            r#"
module child #(parameter int Mode = 0);
    if (Mode == 1) begin : array_override $error("array element selected"); end
    if (Mode == 2) begin : generate_override $error("generate element selected"); end
    if (Mode == 0) begin : unchanged $error("default element retained"); end
endmodule
module top;
    child bank[1:0]();
    for (genvar i = -1; i < 1; i++) begin : lanes
        child dut();
    end
endmodule
"#,
            "indexed",
            "indexed.sv",
        );
        let overrides = ["top.bank[1].Mode=1".to_owned(), "top.lanes[-1].dut.Mode=2".to_owned()];
        let mut compilation = Compilation::new_with_options(&["top".to_owned()], &overrides);
        compilation.add_syntax_tree(&tree);
        let diagnostics = compilation.semantic_diagnostics_with_options(&[]);
        for marker in
            ["array element selected", "generate element selected", "default element retained"]
        {
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.message.contains(marker)),
                "{diagnostics:?}"
            );
        }
    }

    #[test]
    fn library_units_resolve_used_modules_without_instantiating_unused_tops() {
        let unresolved_markers = |library_unit| {
            let mut compilation = Compilation::new();
            compilation.register_source_buffers(&[
                SyntaxTreeBuffer {
                    path: "top.sv".to_owned(),
                    text: "module top; from_library u(); endmodule\n".to_owned(),
                },
                SyntaxTreeBuffer {
                    path: "library.sv".to_owned(),
                    text: "module from_library; endmodule\nmodule unused; unresolved_cell u(); endmodule\n"
                        .to_owned(),
                },
            ]);
            for (path, library) in [("top.sv", false), ("library.sv", library_unit)] {
                compilation.parse_syntax_tree_from_buffer(
                    path,
                    path,
                    &SyntaxTreeOptions::default(),
                    library,
                );
            }
            compilation.semantic_diagnostics_with_options(&[])
        };
        assert!(unresolved_markers(true).is_empty());
        let diagnostics = unresolved_markers(false);
        assert!(diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("unresolved_cell")
                || diagnostic.args.iter().any(|arg| arg.contains("unresolved_cell"))
        }));
    }

    #[test]
    fn named_source_libraries_keep_duplicate_modules_separate() {
        let mut compilation = Compilation::new_with_top_modules(&["chosen:config".to_owned()]);
        let files = [
            ("top.sv", "module top; first a(); second b(); endmodule\n"),
            (
                "config.sv",
                "config chosen; design work.top; default liblist work a b; instance top.a.u use a.cell_type; instance top.b.u use b.cell_type; endconfig\n",
            ),
            ("a/wrapper.sv", "module first; cell_type #(.Expected(1)) u(); endmodule\n"),
            ("b/wrapper.sv", "module second; cell_type #(.Expected(0)) u(); endmodule\n"),
            (
                "a/cell.sv",
                "module cell_type #(parameter bit Expected = 0); if (!Expected) begin : wrong $error(\"wrong first library\"); end endmodule\n",
            ),
            (
                "b/cell.sv",
                "module cell_type #(parameter bit Expected = 1); if (Expected) begin : wrong $error(\"wrong second library\"); end endmodule\n",
            ),
        ];
        let buffers = files
            .map(|(path, text)| SyntaxTreeBuffer { path: path.to_owned(), text: text.to_owned() });
        compilation.register_source_buffers_with_libraries(&buffers, |file| {
            file.split_once('/').map_or("work", |(library, _)| library).to_owned()
        });
        for (file, _) in files {
            compilation.parse_syntax_tree_from_buffer(
                file,
                file,
                &SyntaxTreeOptions::default(),
                false,
            );
        }
        let diagnostics = compilation.semantic_diagnostics_with_options(&[]);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn grouped_files_share_macros_and_declarations_while_projections_keep_their_own_source() {
        let mut compilation = Compilation::new_with_top_modules(&["top".to_owned()]);
        compilation.register_source_buffers(&[
            SyntaxTreeBuffer {
                path: "defs.sv".to_owned(),
                text: "`define VALUE 1'b1\ntypedef logic word_t;\n".to_owned(),
            },
            SyntaxTreeBuffer {
                path: "top.sv".to_owned(),
                text: "module top; word_t q = `VALUE; endmodule\n".to_owned(),
            },
            SyntaxTreeBuffer {
                path: "isolated.sv".to_owned(),
                text: "`ifdef VALUE\ninvalid source;\n`endif\nmodule isolated; endmodule\n"
                    .to_owned(),
            },
        ]);
        let options = SyntaxTreeOptions::default();
        let group = compilation
            .parse_grouped_sources(vec!["defs.sv".to_owned(), "top.sv".to_owned()], &options);
        let defs = Compilation::project_source_file(&group, "defs.sv");
        let top = Compilation::project_source_file(&group, "top.sv");
        assert_eq!(group.buffer_id(), defs.buffer_id());
        assert_ne!(top.buffer_id(), defs.buffer_id());
        compilation.add_syntax_tree(&group);
        compilation.parse_syntax_tree_from_buffer("isolated", "isolated.sv", &options, false);
        assert!(compilation.parse_diagnostics_with_options(&[]).is_empty());
        assert!(compilation.semantic_diagnostics_with_options(&[]).is_empty());
    }

    #[test]
    fn registered_source_buffers_are_available_before_root_parsing() {
        let mut compilation = Compilation::new();
        compilation.register_source_buffers(&[
            SyntaxTreeBuffer {
                path: "root.sv".to_owned(),
                text: "`define HEADER \"header.svh\"\n`include `HEADER\nmodule root; endmodule\n"
                    .to_owned(),
            },
            SyntaxTreeBuffer {
                path: "header.svh".to_owned(),
                text: "`define ROOT_VALUE 1\n".to_owned(),
            },
        ]);

        let tree = compilation.parse_syntax_tree_from_buffer(
            "root",
            "root.sv",
            &SyntaxTreeOptions::default(),
            false,
        );

        assert_eq!(tree.root().kind(), SyntaxKind::COMPILATION_UNIT);
        assert!(compilation.parse_diagnostics_with_options(&[]).is_empty());
    }
}
