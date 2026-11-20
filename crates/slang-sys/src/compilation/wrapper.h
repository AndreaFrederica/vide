#pragma once

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "cxx.h"

#include "../diagnostic/wrapper.h"
#include "../syntax/wrapper.h"
#include "../wrapper.h"
#include "slang/ast/Compilation.h"

namespace slang_sys::compilation {

struct ParseSyntaxTreeOptions;

class Compilation {
  public:
    Compilation(std::vector<std::string> top_modules, std::vector<std::string> parameter_overrides);

    std::vector<std::string> top_modules;
    std::shared_ptr<syntax::SourceSession> session;
    std::unique_ptr<::slang::ast::Compilation> inner;
};

std::unique_ptr<Compilation> new_compilation(rust::Vec<rust::String> top_modules, rust::Vec<rust::String> parameter_overrides);
std::shared_ptr<syntax::SyntaxTree> parse_syntax_tree_from_text(
    Compilation& compilation,
    rust::Str text,
    rust::Str name,
    rust::Str path,
    ParseSyntaxTreeOptions options
);
void register_source_buffers(
    Compilation& compilation,
    rust::Vec<rust::String> paths,
    rust::Vec<rust::String> texts,
    rust::Vec<rust::String> libraries
);
std::shared_ptr<syntax::SyntaxTree> parse_syntax_tree_from_buffer(
    Compilation& compilation,
    rust::Str name,
    rust::Str path,
    ParseSyntaxTreeOptions options,
    bool library_unit
);
std::shared_ptr<syntax::SyntaxTree> parse_grouped_sources(
    Compilation& compilation,
    rust::Vec<rust::String> paths,
    rust::Vec<rust::String> predefines,
    rust::Vec<rust::String> include_paths
);
std::shared_ptr<syntax::SyntaxTree> project_source_file(
    const syntax::SyntaxTree& group, rust::Str path
);
std::shared_ptr<syntax::SyntaxTree> parse_library_map_syntax_tree_from_text(
    Compilation& compilation,
    rust::Str text,
    rust::Str name,
    rust::Str path
);
std::shared_ptr<syntax::SyntaxTree> parse_library_map_syntax_tree_from_buffer(
    Compilation& compilation,
    rust::Str name,
    rust::Str path,
    bool collect_expected_syntax,
    std::size_t expected_syntax_offset,
    bool has_expected_syntax_offset
);
void add_syntax_tree(Compilation& compilation, std::shared_ptr<syntax::SyntaxTree> tree);
rust::Vec<diagnostic::RawSyntaxDiagnostic> parse_diagnostics(
    const Compilation& compilation,
    rust::Vec<rust::String> warning_options
);
rust::Vec<diagnostic::RawSyntaxDiagnostic> semantic_diagnostics(
    const Compilation& compilation,
    rust::Vec<rust::String> warning_options
);
} // namespace slang_sys::compilation
