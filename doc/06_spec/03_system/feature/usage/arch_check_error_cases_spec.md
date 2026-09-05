# Architecture Check Error Cases

> Tests failure paths and edge cases in the architecture validation system. Covers boundary conditions for string trimming, pattern list parsing, import pattern matching with glob-style wildcards, allow/deny rule evaluation, import statement extraction from source content, and module path resolution.

<!-- sdn-diagram:id=arch_check_error_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arch_check_error_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arch_check_error_cases_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arch_check_error_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Architecture Check Error Cases

Tests failure paths and edge cases in the architecture validation system. Covers boundary conditions for string trimming, pattern list parsing, import pattern matching with glob-style wildcards, allow/deny rule evaluation, import statement extraction from source content, and module path resolution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ARCH-001 |
| Category | Tooling |
| Status | Active |
| Source | `test/03_system/feature/usage/arch_check_error_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests failure paths and edge cases in the architecture validation system.
Covers boundary conditions for string trimming, pattern list parsing,
import pattern matching with glob-style wildcards, allow/deny rule evaluation,
import statement extraction from source content, and module path resolution.

## Syntax

```simple
val result = _match_pattern("core/lexer", "core/*")
val allowed = _is_import_allowed("core/ast", rule)
```
Arch Check Error Cases - Negative/Edge Path Tests

Tests failure paths and edge cases in architecture validation:
- empty/degenerate inputs to pattern matching
- pattern boundary conditions
- import parsing edge cases
- rule evaluation with empty allow/deny lists

Feature: 8 (Architecture Validation)
Source: src/app/cli/arch_check.spl

## Scenarios

### Arch Check Error Cases: _str_trim edge cases

#### handles already-trimmed string unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("clean")).to_equal("clean")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("")).to_equal("")
```

</details>

#### handles string of only spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("   ")).to_equal("")
```

</details>

#### handles string of only tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("\t\t")).to_equal("")
```

</details>

#### handles single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("x")).to_equal("x")
```

</details>

#### handles string with tab and spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_str_trim("\t  hello  \t")).to_equal("hello")
```

</details>

### Arch Check Error Cases: _parse_pattern_list edge cases

#### returns empty list for empty brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = []")
expect(result.len()).to_equal(0)
```

</details>

#### returns empty list for missing brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = core")
expect(result.len()).to_equal(0)
```

</details>

#### returns empty list for empty input string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("")
expect(result.len()).to_equal(0)
```

</details>

#### parses single quoted pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = ['core/**']")
expect(result[0]).to_equal("core/**")
expect(result.len()).to_equal(1)
```

</details>

#### parses single item with double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("allow = [\"core/**\"]")
expect(result[0]).to_equal("core/**")
expect(result.len()).to_equal(1)
```

</details>

#### ignores whitespace around patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_pattern_list("deny = [ \"compiler/**\" ]")
expect(result[0]).to_equal("compiler/**")
expect(result.len()).to_equal(1)
```

</details>

### Arch Check Error Cases: _match_pattern edge cases

#### empty pattern does not match non-empty import

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/lexer", "")
expect(result).to_equal(false)
```

</details>

#### empty import does not match non-empty pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("", "core/lexer")
expect(result).to_equal(false)
```

</details>

#### empty import matches empty pattern exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("", "")
expect(result).to_equal(true)
```

</details>

#### /** suffix matches any subpath of prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("a/b/c", "a/**")
expect(result).to_equal(true)
```

</details>

#### pattern exact does not match import with extra segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/lexer/extra", "core/lexer")
expect(result).to_equal(true)
```

</details>

#### /* does not match two levels deep

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/lexer/submodule", "core/*")
expect(result).to_equal(false)
```

</details>

#### /* matches single level sub-path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/lexer", "core/*")
expect(result).to_equal(true)
```

</details>

#### prefix match requires slash boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("compiler_other/ast", "compiler")
expect(result).to_equal(false)
```

</details>

#### exact match succeeds for identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("std/text", "std/text")
expect(result).to_equal(true)
```

</details>

#### pattern with /** matches direct child

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast", "core/**")
expect(result).to_equal(true)
```

</details>

### Arch Check Error Cases: _is_import_allowed edge cases

#### import allowed when both allow and deny lists are empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: []
)
expect(_is_import_allowed("any/import", rule)).to_equal(true)
```

</details>

#### import denied when not in non-empty allow list

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: []
)
expect(_is_import_allowed("compiler/backend", rule)).to_equal(false)
```

</details>

#### import allowed when in allow list and deny list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: []
)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
```

</details>

#### import denied when matched by deny pattern even if in allow list

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"]
)
expect(_is_import_allowed("core/compiler/backend", rule)).to_equal(false)
```

</details>

#### import allowed when in allow but not in deny

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"]
)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
```

</details>

### Arch Check Error Cases: _parse_imports_from_content edge cases

#### returns empty list for empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_imports_from_content("")
expect(result.len()).to_equal(0)
```

</details>

#### returns empty list for content with no use statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "fn main():\n    print \"hello\"\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### ignores comment lines starting with #

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# use app.io.mod (file_read)\nfn foo(): ()\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### strips trailing dot from module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use std.text. (\n)\n"
val result = _parse_imports_from_content(content)
expect(result[0]).to_equal("std/text")
expect(result.len()).to_equal(1)
```

</details>

#### converts dot notation to slash notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler.frontend.core.ast (CoreExpr)\n"
val result = _parse_imports_from_content(content)
expect(result[0]).to_equal("compiler/frontend/core/ast")
expect(result.len()).to_equal(1)
```

</details>

### Arch Check Error Cases: _module_path_from_init_file edge cases

#### returns __init__.spl when init file is directly under root with no subdir

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When path is /project/__init__.spl and root is /project:
# after removing root prefix: /__init__.spl
# after removing leading /: __init__.spl
# __init__.spl does not end with /__init__.spl so suffix is not stripped
# Result is "__init__.spl" not ""
val path = "/project/__init__.spl"
val root = "/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("__init__.spl")
```

</details>

#### handles path not under root unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/other/__init__.spl"
val root = "/project"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("/other")
```

</details>

### Arch Check Error Cases: _file_is_under_module edge cases

#### empty module path matches any file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _file_is_under_module("/project/src/anything.spl", "", "/project")
expect(result).to_equal(true)
```

</details>

#### file at exact module boundary matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _file_is_under_module("/project/src/compiler/10.frontend/core/file.spl", "src/compiler/10.frontend/core", "/project")
expect(result).to_equal(true)
```

</details>

#### file outside module boundary does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _file_is_under_module("/project/src/compiler/70.backend/file.spl", "src/compiler/10.frontend/core", "/project")
expect(result).to_equal(false)
```

</details>

#### file with similar prefix but different module does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _file_is_under_module("/project/src/compiler/10.frontend/core_ext/file.spl", "src/compiler/10.frontend/core", "/project")
expect(result).to_equal(false)
```

</details>

### Arch Check Error Cases: _parse_arch_block edge cases

#### returns false for empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _parse_arch_block("")
expect(result.0).to_equal(false)
```

</details>

#### returns true when arch keyword appears in comment because parser has no comment awareness

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser uses content.contains("arch {") which matches in comments too.
# This documents the known limitation: comments are not stripped before scanning.
val content = "# arch { deny = [] }\nfn foo(): ()\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
```

</details>

#### returns empty allow and deny for arch block with no imports section

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  dimension = \"entity\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(0)
expect(result.2.len()).to_equal(0)
```

</details>

#### parses arch block with empty allow list

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = []\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(0)
```

</details>

#### parses arch block with empty deny list

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    deny = []\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.2.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
