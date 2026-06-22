# Arch Check System Specification

> <details>

<!-- sdn-diagram:id=arch_check_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arch_check_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arch_check_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arch_check_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arch Check System Specification

## Scenarios

### arch_check system: Phase 1 - Pattern matching rules

#### exact pattern matches exact import path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast", "core/ast")
expect(result).to_equal(true)
```

</details>

#### exact pattern does not match different path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast", "std/text")
expect(result).to_equal(false)
```

</details>

#### wildcard /** matches direct child path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("compiler/backend", "compiler/**")
expect(result).to_equal(true)
```

</details>

#### wildcard /** matches deeply nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("compiler/feature/lexing/token", "compiler/**")
expect(result).to_equal(true)
```

</details>

#### wildcard /** does not match sibling path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast", "compiler/**")
expect(result).to_equal(false)
```

</details>

#### wildcard /* matches single level child

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("std/text", "std/*")
expect(result).to_equal(true)
```

</details>

#### wildcard /* does not match multi-level path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("std/text/util", "std/*")
expect(result).to_equal(false)
```

</details>

#### prefix match with slash boundary applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("compiler/backend/jit", "compiler/backend")
expect(result).to_equal(true)
```

</details>

#### partial prefix without boundary does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("compiler_other/ast", "compiler")
expect(result).to_equal(false)
```

</details>

#### exact match of top-level module works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("std", "std")
expect(result).to_equal(true)
```

</details>

#### pattern does not match empty import path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("", "core/ast")
expect(result).to_equal(false)
```

</details>

#### /** prefix is stripped correctly for matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast/parser", "core/**")
expect(result).to_equal(true)
```

</details>

#### /* prefix is stripped correctly for matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core/ast", "core/*")
expect(result).to_equal(true)
```

</details>

#### /* requires at least one path component after prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _match_pattern("core", "core/*")
expect(result).to_equal(false)
```

</details>

### arch_check system: Phase 2 - Rule parsing

#### detects absence of arch block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# no arch block here\nfn main():\n    pass\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(false)
```

</details>

#### detects presence of arch block

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  dimension = \"service\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
```

</details>

#### parses allow list with single pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = [\"core/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
val allow_list = result.1
expect(allow_list.len()).to_equal(1)
expect(allow_list[0]).to_equal("core/**")
```

</details>

#### parses allow list with multiple patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = [\"core/**\", \"std/**\", \"shared\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
val allow_list = result.1
expect(allow_list.len()).to_equal(3)
expect(allow_list[0]).to_equal("core/**")
expect(allow_list[1]).to_equal("std/**")
expect(allow_list[2]).to_equal("shared")
```

</details>

#### parses deny list with single pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    deny = [\"compiler/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
val deny = result.2
expect(deny.len()).to_equal(1)
expect(deny[0]).to_equal("compiler/**")
```

</details>

#### parses deny list with multiple patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    deny = [\"compiler/**\", \"app/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
val deny = result.2
expect(deny.len()).to_equal(2)
expect(deny[0]).to_equal("compiler/**")
expect(deny[1]).to_equal("app/**")
```

</details>

#### parses both allow and deny lists together

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  imports {\n"
content = content + "    allow = [\"core/**\", \"std/**\"]\n"
content = content + "    deny = [\"core/compiler/**\"]\n"
content = content + "  }\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(2)
expect(result.2.len()).to_equal(1)
expect(result.2[0]).to_equal("core/compiler/**")
```

</details>

#### returns empty patterns when no imports block present

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "arch {\n"
content = content + "  dimension = \"entity\"\n"
content = content + "  visibility = \"private\"\n"
content = content + "}\n"
val result = _parse_arch_block(content)
expect(result.0).to_equal(true)
expect(result.1.len()).to_equal(0)
expect(result.2.len()).to_equal(0)
```

</details>

#### parses pattern list with single-quoted strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "allow = ['core/**', 'std/**']"
val result = _parse_pattern_list(line)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("core/**")
expect(result[1]).to_equal("std/**")
```

</details>

#### returns empty list when no brackets found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "allow = core, std"
val result = _parse_pattern_list(line)
expect(result.len()).to_equal(0)
```

</details>

#### returns empty list for empty bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "deny = []"
val result = _parse_pattern_list(line)
expect(result.len()).to_equal(0)
```

</details>

### arch_check system: Phase 3 - Import scanning

#### extracts single use statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler_core.ast (AstNode)\nfn main():\n    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("compiler_core/ast")
```

</details>

#### extracts multiple use statements

1. var content = "use compiler core ast
2. content = content + "use app io mod
   - Expected: result.len() equals `2`
   - Expected: result[0] equals `compiler_core/ast`
   - Expected: result[1] equals `app/io/mod`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "use compiler_core.ast (AstNode)\n"
content = content + "\n"
content = content + "use app.io.mod (shell)\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("compiler_core/ast")
expect(result[1]).to_equal("app/io/mod")
```

</details>

#### converts dot notation to slash notation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use app.desugar.trait_scanner (scan_traits)\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/desugar/trait_scanner")
```

</details>

#### ignores comment lines

1. var content = "# use compiler core ast
2. content = content + "fn foo
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "# use compiler_core.ast (AstNode)\n"
content = content + "fn foo():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### ignores non-use lines

1. content = content + "fn bar
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = "struct Foo:\n"
content = content + "    x: i64\n"
content = content + "fn bar():\n"
content = content + "    pass\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### handles use with wildcard syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use std.text.*\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("std/text")
```

</details>

#### strips trailing dot from module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use app.io.\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("app/io")
```

</details>

#### handles empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ""
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(0)
```

</details>

#### extracts deeply nested module paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler.backend.jit.codegen (JitBackend)\n"
val result = _parse_imports_from_content(content)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("compiler/backend/jit/codegen")
```

</details>

### arch_check system: Phase 4 - Rule application

#### allows import when no rules defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: []
)
val result = _is_import_allowed("anything/at/all", rule)
expect(result).to_equal(true)
```

</details>

#### denies import matching deny pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"]
)
val result = _is_import_allowed("compiler/backend", rule)
expect(result).to_equal(false)
```

</details>

#### allows import not matching any deny pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: [],
    deny_patterns: ["compiler/**"]
)
val result = _is_import_allowed("core/ast", rule)
expect(result).to_equal(true)
```

</details>

#### allows import matching allow pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**", "std/**"],
    deny_patterns: []
)
val result = _is_import_allowed("core/ast", rule)
expect(result).to_equal(true)
```

</details>

#### denies import not matching any allow pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**", "std/**"],
    deny_patterns: []
)
val result = _is_import_allowed("app/io", rule)
expect(result).to_equal(false)
```

</details>

#### deny takes precedence over allow

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"]
)
val result = _is_import_allowed("core/compiler/backend", rule)
expect(result).to_equal(false)
```

</details>

#### allows other paths when deny only targets subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "src/__init__.spl",
    module_path: "src",
    allow_patterns: ["core/**"],
    deny_patterns: ["core/compiler/**"]
)
val result = _is_import_allowed("core/ast", rule)
expect(result).to_equal(true)
```

</details>

#### file under module path matches correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/core/ast.spl"
val result = _file_is_under_module(file, "src/core", "/project")
expect(result).to_equal(true)
```

</details>

#### file not under module path does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/compiler/backend.spl"
val result = _file_is_under_module(file, "src/core", "/project")
expect(result).to_equal(false)
```

</details>

#### empty module path matches all files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "/project/src/any/file.spl"
val result = _file_is_under_module(file, "", "/project")
expect(result).to_equal(true)
```

</details>

#### module path extraction from deeply nested init file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/workspace/src/compiler/backend/jit/__init__.spl"
val root = "/workspace"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/compiler/backend/jit")
```

</details>

#### module path extraction strips root prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/home/user/myproject/src/core/__init__.spl"
val root = "/home/user/myproject"
val result = _module_path_from_init_file(path, root)
expect(result).to_equal("src/core")
```

</details>

### arch_check system: Phase 5 - Full validation

#### arch_check.spl source file exists in project

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("test -f src/app/cli/arch_check.spl && echo yes")
val trimmed = result.stdout.trim()
expect(trimmed).to_equal("yes")
```

</details>

#### arch_check exports run_arch_check function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -c 'fn run_arch_check' src/app/cli/arch_check.spl")
val count = int(result.stdout.trim())
expect(count > 0).to_equal(true)
```

</details>

#### arch_check exports scan_arch_rules function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -c 'fn scan_arch_rules' src/app/cli/arch_check.spl")
val count = int(result.stdout.trim())
expect(count > 0).to_equal(true)
```

</details>

#### arch_check exports check_arch function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -c 'fn check_arch' src/app/cli/arch_check.spl")
val count = int(result.stdout.trim())
expect(count > 0).to_equal(true)
```

</details>

#### check-arch is registered in main CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("grep -c 'check-arch' src/app/cli/main.spl")
val count = int(result.stdout.trim())
expect(count > 0).to_equal(true)
```

</details>

#### string trimming handles tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("\thello\t")
expect(result).to_equal("hello")
```

</details>

#### string trimming handles carriage returns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("hello\r")
expect(result).to_equal("hello")
```

</details>

#### string trimming returns empty for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _str_trim("   \t  ")
expect(result).to_equal("")
```

</details>

#### pattern matching handles path with multiple segments correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# core/ast matches the exact path "core/ast"
expect(_match_pattern("core/ast", "core/ast")).to_equal(true)
# core/parser is also matched if we use core/**
expect(_match_pattern("core/parser", "core/**")).to_equal(true)
# compiler does not match core/**
expect(_match_pattern("compiler/ast", "core/**")).to_equal(false)
```

</details>

#### combined allow and deny rules work end-to-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = ArchRule(
    init_file: "/project/src/app/__init__.spl",
    module_path: "src/app",
    allow_patterns: ["std/**", "core/**"],
    deny_patterns: ["core/compiler/**"]
)
# Allowed paths
expect(_is_import_allowed("std/text", rule)).to_equal(true)
expect(_is_import_allowed("core/ast", rule)).to_equal(true)
# Denied by explicit deny
expect(_is_import_allowed("core/compiler/backend", rule)).to_equal(false)
# Denied by not matching allow (app/io not in allow list)
expect(_is_import_allowed("app/io", rule)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/arch_check_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- arch_check system: Phase 1 - Pattern matching rules
- arch_check system: Phase 2 - Rule parsing
- arch_check system: Phase 3 - Import scanning
- arch_check system: Phase 4 - Rule application
- arch_check system: Phase 5 - Full validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
