# Depgraph Specification

> Tests covering Dependency Graph Generator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Depgraph Specification

## Scenarios

### Dependency Graph Generator

#### Directory Scanning

#### finds all .spl files in directory

- finds all .spl files in directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds all .spl files in directory")
# scanner.scan_directory("./test_dir", recursive=false)
# should return list of .spl files in directory
val files = ["module1.spl", "module2.spl", "helper.spl"]
expect files.len() == 3
```

</details>

#### excludes .__init__.spl from scan

- excludes .__init__.spl from scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes .__init__.spl from scan")
# Dot-prefixed files are generated, not source
val files = ["module1.spl", ".__init__.spl", "module2.spl"]
val filtered = files.filter(not _1.starts_with("."))
expect filtered.len() == 2
```

</details>

#### excludes __init__.spl from module list

- excludes __init__.spl from module list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes __init__.spl from module list")
# __init__.spl is manifest, not a module
val files = ["module1.spl", "__init__.spl", "module2.spl"]
val modules = files.filter(_1 != "__init__.spl")
expect modules.len() == 2
```

</details>

#### identifies child directories with __init__.spl

- identifies child directories with __init__.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies child directories with __init__.spl")
# Directories with __init__.spl are child modules
val has_init = true
expect has_init == true
```

</details>

#### skips directories without __init__.spl

- skips directories without __init__.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips directories without __init__.spl")
# Directories without __init__.spl are not modules
val has_init = false
expect has_init == false
```

</details>

#### Import Extraction

#### extracts use statements

- extracts use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts use statements")
val source = "use std.io\nuse core.json"
val imports = ["std.io", "core.json"]
expect imports.len() == 2
```

</details>

#### extracts export use statements

- extracts export use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts export use statements")
val source = "export use router.Router"
val exports = ["router.Router"]
expect exports.len() == 1
```

</details>

#### extracts common use statements

- extracts common use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts common use statements")
val source = "common use core.prelude"
val common = ["core.prelude.*"]
expect common.len() == 1
```

</details>

#### extracts glob imports

- extracts glob imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts glob imports")
val source = "use std.collections"
val imports = ["std.collections.*"]
expect imports[0].ends_with(".*")
```

</details>

#### extracts grouped imports

- extracts grouped imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts grouped imports")
val source = "use std.{io, fs, net}"
val imports = ["std.io", "std.fs", "std.net"]
expect imports.len() == 3
```

</details>

#### extracts aliased imports

- extracts aliased imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts aliased imports")
val source = "use std.collections as col"
val imports = [("std.collections", "col")]
expect imports.len() == 1
```

</details>

#### External Dependency Detection

#### identifies imports outside module tree

- identifies imports outside module tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies imports outside module tree")
val module_path = "myapp.server"
val import_path = "std.io"
val is_external = not import_path.starts_with("myapp.")
expect is_external == true
```

</details>

#### marks stdlib imports as external

- marks stdlib imports as external


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks stdlib imports as external")
val import_path = "std.collections"
val is_stdlib = import_path.starts_with("std.")
expect is_stdlib == true
```

</details>

#### marks core imports as external

- marks core imports as external


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks core imports as external")
val import_path = "core.json"
val is_core = import_path.starts_with("core.")
expect is_core == true
```

</details>

#### identifies internal imports

- identifies internal imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies internal imports")
val module_path = "myapp.server"
val import_path = "myapp.utils"
val is_internal = import_path.starts_with("myapp.")
expect is_internal == true
```

</details>

#### identifies sibling imports

- identifies sibling imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies sibling imports")
val module_path = "myapp.server.handler"
val import_path = "myapp.server.router"
val is_sibling = true  # Same parent
expect is_sibling == true
```

</details>

#### Child Blocking Rules

#### blocks child exports unless parent has pub mod

- blocks child exports unless parent has pub mod


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks child exports unless parent has pub mod")
# Child module cannot export unless parent declares: pub mod child
val parent_has_pub_mod = false
val child_can_export = parent_has_pub_mod
expect child_can_export == false
```

</details>

#### allows child exports when parent has pub mod

- allows child exports when parent has pub mod


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows child exports when parent has pub mod")
val parent_has_pub_mod = true
val child_can_export = parent_has_pub_mod
expect child_can_export == true
```

</details>

#### blocks symbols not in parent export use

- blocks symbols not in parent export use


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks symbols not in parent export use")
# Even with pub mod, symbol must be in export use
val parent_has_pub_mod = true
val in_export_list = false
val symbol_visible = parent_has_pub_mod and in_export_list
expect symbol_visible == false
```

</details>

#### allows symbols in parent export use

- allows symbols in parent export use


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows symbols in parent export use")
val parent_has_pub_mod = true
val in_export_list = true
val symbol_visible = parent_has_pub_mod and in_export_list
expect symbol_visible == true
```

</details>

#### glob export includes non-macro public items

- glob export includes non-macro public items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("glob export includes non-macro public items")
# export use child includes all pub non-macro items
val has_glob_export = true
val is_macro = false
val is_public = true
val visible = has_glob_export and is_public and not is_macro
expect visible == true
```

</details>

#### glob export excludes macros unless auto import

- glob export excludes macros unless auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("glob export excludes macros unless auto import")
val has_glob_export = true
val is_macro = true
val in_auto_import = false
val visible = has_glob_export and is_macro and in_auto_import
expect visible == false
```

</details>

#### .__init__.spl Generation

#### generates dot-prefixed file

- generates dot-prefixed file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates dot-prefixed file")
val output_name = ".__init__.spl"
expect output_name.starts_with(".")
```

</details>

#### includes header comment

- includes header comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes header comment")
val header = "# Auto-generated dependency analysis"
expect header.starts_with("#")
```

</details>

#### includes external dependency list

- includes external dependency list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes external dependency list")
val externals = ["std.io", "core.json"]
val comments = externals.map("# external: " + _1)
expect comments.len() == 2
```

</details>

#### includes child module declarations

- includes child module declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes child module declarations")
val children = ["scanner", "parser", "analyzer"]
val mods = children.map("mod " + _1)
expect mods.len() == 3
```

</details>

#### includes pub mod for public children

- includes pub mod for public children


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes pub mod for public children")
val public_children = ["api", "types"]
val pub_mods = public_children.map("pub mod " + _1)
expect pub_mods[0] == "pub mod api"
```

</details>

#### includes export use statements

- includes export use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes export use statements")
val exports = ["scanner.scan_directory", "analyzer.analyze"]
val export_stmts = exports.map("export use " + _1)
expect export_stmts.len() == 2
```

</details>

#### preserves existing manual exports

- preserves existing manual exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves existing manual exports")
# If __init__.spl exists with manual exports, preserve them
val manual_exports = ["special.CustomType"]
expect manual_exports.len() == 1
```

</details>

#### Recursive Mode

#### processes subdirectories when recursive=true

- processes subdirectories when recursive=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes subdirectories when recursive=true")
val recursive = true
val process_children = recursive
expect process_children == true
```

</details>

#### skips subdirectories when recursive=false

- skips subdirectories when recursive=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips subdirectories when recursive=false")
val recursive = false
val process_children = recursive
expect process_children == false
```

</details>

#### generates .__init__.spl for each directory

- generates .__init__.spl for each directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates .__init__.spl for each directory")
val dirs = ["src/", "src/api/", "src/utils/"]
val generated = dirs.map(_1 + ".__init__.spl")
expect generated.len() == 3
```

</details>

#### AOP Logging

#### logs directory scan start

- logs directory scan start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs directory scan start")
val log_msg = "[SCAN] Starting scan: ./src"
expect log_msg.contains("[SCAN]")
```

</details>

#### logs each file processed

- logs each file processed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs each file processed")
val log_msg = "[FILE] Processing: module.spl"
expect log_msg.contains("[FILE]")
```

</details>

#### logs external dependencies found

- logs external dependencies found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs external dependencies found")
val log_msg = "[DEP] External: std.io"
expect log_msg.contains("[DEP]")
```

</details>

#### logs child modules found

- logs child modules found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs child modules found")
val log_msg = "[MOD] Child: utils"
expect log_msg.contains("[MOD]")
```

</details>

#### logs generation complete

- logs generation complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs generation complete")
val log_msg = "[GEN] Generated: .__init__.spl"
expect log_msg.contains("[GEN]")
```

</details>

#### CLI Interface

#### accepts directory argument

- accepts directory argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts directory argument")
val args = ["simple_depgraph", "./src"]
expect args.len() >= 2
```

</details>

#### accepts --recursive flag

- accepts --recursive flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts --recursive flag")
val args = ["simple_depgraph", "./src", "--recursive"]
val has_recursive = args.contains("--recursive")
expect has_recursive == true
```

</details>

#### accepts --verbose flag for detailed logging

- accepts --verbose flag for detailed logging


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts --verbose flag for detailed logging")
val args = ["simple_depgraph", "./src", "--verbose"]
val has_verbose = args.contains("--verbose")
expect has_verbose == true
```

</details>

#### shows usage on no arguments

- shows usage on no arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows usage on no arguments")
val args = ["simple_depgraph"]
val show_usage = args.len() < 2
expect show_usage == true
```

</details>

#### returns exit code 0 on success

- returns exit code 0 on success


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exit code 0 on success")
val exit_code = 0
expect exit_code == 0
```

</details>

#### returns exit code 1 on error

- returns exit code 1 on error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exit code 1 on error")
val exit_code = 1
expect exit_code == 1
```

</details>

#### Error Handling

#### reports file read errors

- reports file read errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports file read errors")
val error = "Failed to read: module.spl"
expect error.contains("Failed to read")
```

</details>

#### reports directory not found

- reports directory not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports directory not found")
val error = "Directory not found: ./nonexistent"
expect error.contains("not found")
```

</details>

#### reports parse errors

- reports parse errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports parse errors")
val error = "Parse error in module.spl:10"
expect error.contains("Parse error")
```

</details>

#### continues on non-fatal errors

- continues on non-fatal errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues on non-fatal errors")
val continue_on_error = true
expect continue_on_error == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/depgraph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Dependency Graph Generator.
- Dependency Graph Generator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f22e701d54c37488fab9d7c18d1c17a6555289093eb2a27a9888f9ecc1179740`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f22e701d54c37488fab9d7c18d1c17a6555289093eb2a27a9888f9ecc1179740`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f22e701d54c37488fab9d7c18d1c17a6555289093eb2a27a9888f9ecc1179740`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/depgraph_spec.spl
mirror: doc/06_spec/unit/app/tooling/depgraph_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/depgraph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/depgraph_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/depgraph_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds all .spl files in directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/depgraph_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes .__init__.spl from scan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/depgraph_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'excludes __init__.spl from module list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
