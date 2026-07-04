# Dependency Graph Generator Specification

> Tool for auto-generating .__init__.spl files with dependency analysis.

<!-- sdn-diagram:id=depgraph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=depgraph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

depgraph_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=depgraph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependency Graph Generator Specification

Tool for auto-generating .__init__.spl files with dependency analysis.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3100 |
| Category | Tooling |
| Status | Planned |
| Source | `test/01_unit/app/tooling/depgraph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tool for auto-generating .__init__.spl files with dependency analysis.
Scans directories for .spl files, extracts imports, identifies external
dependencies, and enforces child module visibility rules via parent
re-export declarations.

## Scenarios

### Dependency Graph Generator

#### Directory Scanning

#### finds all .spl files in directory

1. expect files len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# scanner.scan_directory("./test_dir", recursive=false)
# should return list of .spl files in directory
val files = ["module1.spl", "module2.spl", "helper.spl"]
expect files.len() == 3
```

</details>

#### excludes .__init__.spl from scan

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Dot-prefixed files are generated, not source
val files = ["module1.spl", ".__init__.spl", "module2.spl"]
val filtered = files.filter(not _1.starts_with("."))
expect filtered.len() == 2
```

</details>

#### excludes __init__.spl from module list

1. expect modules len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# __init__.spl is manifest, not a module
val files = ["module1.spl", "__init__.spl", "module2.spl"]
val modules = files.filter(_1 != "__init__.spl")
expect modules.len() == 2
```

</details>

#### identifies child directories with __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Directories with __init__.spl are child modules
val has_init = true
expect has_init == true
```

</details>

#### skips directories without __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Directories without __init__.spl are not modules
val has_init = false
expect has_init == false
```

</details>

#### Import Extraction

#### extracts use statements

1. expect imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.io\nuse core.json"
val imports = ["std.io", "core.json"]
expect imports.len() == 2
```

</details>

#### extracts export use statements

1. expect exports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "export use router.Router"
val exports = ["router.Router"]
expect exports.len() == 1
```

</details>

#### extracts common use statements

1. expect common len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "common use core.prelude"
val common = ["core.prelude.*"]
expect common.len() == 1
```

</details>

#### extracts glob imports

1. expect imports[0] ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.collections"
val imports = ["std.collections.*"]
expect imports[0].ends_with(".*")
```

</details>

#### extracts grouped imports

1. expect imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.{io, fs, net}"
val imports = ["std.io", "std.fs", "std.net"]
expect imports.len() == 3
```

</details>

#### extracts aliased imports

1. expect imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.collections as col"
val imports = [("std.collections", "col")]
expect imports.len() == 1
```

</details>

#### External Dependency Detection

#### identifies imports outside module tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "myapp.server"
val import_path = "std.io"
val is_external = not import_path.starts_with("myapp.")
expect is_external == true
```

</details>

#### marks stdlib imports as external

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val import_path = "std.collections"
val is_stdlib = import_path.starts_with("std.")
expect is_stdlib == true
```

</details>

#### marks core imports as external

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val import_path = "core.json"
val is_core = import_path.starts_with("core.")
expect is_core == true
```

</details>

#### identifies internal imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "myapp.server"
val import_path = "myapp.utils"
val is_internal = import_path.starts_with("myapp.")
expect is_internal == true
```

</details>

#### identifies sibling imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_path = "myapp.server.handler"
val import_path = "myapp.server.router"
val is_sibling = true  # Same parent
expect is_sibling == true
```

</details>

#### Child Blocking Rules

#### blocks child exports unless parent has pub mod

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Child module cannot export unless parent declares: pub mod child
val parent_has_pub_mod = false
val child_can_export = parent_has_pub_mod
expect child_can_export == false
```

</details>

#### allows child exports when parent has pub mod

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_has_pub_mod = true
val child_can_export = parent_has_pub_mod
expect child_can_export == true
```

</details>

#### blocks symbols not in parent export use

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Even with pub mod, symbol must be in export use
val parent_has_pub_mod = true
val in_export_list = false
val symbol_visible = parent_has_pub_mod and in_export_list
expect symbol_visible == false
```

</details>

#### allows symbols in parent export use

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_has_pub_mod = true
val in_export_list = true
val symbol_visible = parent_has_pub_mod and in_export_list
expect symbol_visible == true
```

</details>

#### glob export includes non-macro public items

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# export use child includes all pub non-macro items
val has_glob_export = true
val is_macro = false
val is_public = true
val visible = has_glob_export and is_public and not is_macro
expect visible == true
```

</details>

#### glob export excludes macros unless auto import

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_glob_export = true
val is_macro = true
val in_auto_import = false
val visible = has_glob_export and is_macro and in_auto_import
expect visible == false
```

</details>

#### .__init__.spl Generation

#### generates dot-prefixed file

1. expect output name starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_name = ".__init__.spl"
expect output_name.starts_with(".")
```

</details>

#### includes header comment

1. expect header starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "# Auto-generated dependency analysis"
expect header.starts_with("#")
```

</details>

#### includes external dependency list

1. expect comments len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val externals = ["std.io", "core.json"]
val comments = externals.map("# external: " + _1)
expect comments.len() == 2
```

</details>

#### includes child module declarations

1. expect mods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val children = ["scanner", "parser", "analyzer"]
val mods = children.map("mod " + _1)
expect mods.len() == 3
```

</details>

#### includes pub mod for public children

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val public_children = ["api", "types"]
val pub_mods = public_children.map("pub mod " + _1)
expect pub_mods[0] == "pub mod api"
```

</details>

#### includes export use statements

1. expect export stmts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = ["scanner.scan_directory", "analyzer.analyze"]
val export_stmts = exports.map("export use " + _1)
expect export_stmts.len() == 2
```

</details>

#### preserves existing manual exports

1. expect manual exports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If __init__.spl exists with manual exports, preserve them
val manual_exports = ["special.CustomType"]
expect manual_exports.len() == 1
```

</details>

#### Recursive Mode

#### processes subdirectories when recursive=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recursive = true
val process_children = recursive
expect process_children == true
```

</details>

#### skips subdirectories when recursive=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recursive = false
val process_children = recursive
expect process_children == false
```

</details>

#### generates .__init__.spl for each directory

1. expect generated len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = ["src/", "src/api/", "src/utils/"]
val generated = dirs.map(_1 + ".__init__.spl")
expect generated.len() == 3
```

</details>

#### AOP Logging

#### logs directory scan start

1. expect log msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_msg = "[SCAN] Starting scan: ./src"
expect log_msg.contains("[SCAN]")
```

</details>

#### logs each file processed

1. expect log msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_msg = "[FILE] Processing: module.spl"
expect log_msg.contains("[FILE]")
```

</details>

#### logs external dependencies found

1. expect log msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_msg = "[DEP] External: std.io"
expect log_msg.contains("[DEP]")
```

</details>

#### logs child modules found

1. expect log msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_msg = "[MOD] Child: utils"
expect log_msg.contains("[MOD]")
```

</details>

#### logs generation complete

1. expect log msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_msg = "[GEN] Generated: .__init__.spl"
expect log_msg.contains("[GEN]")
```

</details>

#### CLI Interface

#### accepts directory argument

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple_depgraph", "./src"]
expect args.len() >= 2
```

</details>

#### accepts --recursive flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple_depgraph", "./src", "--recursive"]
val has_recursive = args.contains("--recursive")
expect has_recursive == true
```

</details>

#### accepts --verbose flag for detailed logging

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple_depgraph", "./src", "--verbose"]
val has_verbose = args.contains("--verbose")
expect has_verbose == true
```

</details>

#### shows usage on no arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple_depgraph"]
val show_usage = args.len() < 2
expect show_usage == true
```

</details>

#### returns exit code 0 on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 0
expect exit_code == 0
```

</details>

#### returns exit code 1 on error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 1
expect exit_code == 1
```

</details>

#### Error Handling

#### reports file read errors

1. expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "Failed to read: module.spl"
expect error.contains("Failed to read")
```

</details>

#### reports directory not found

1. expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "Directory not found: ./nonexistent"
expect error.contains("not found")
```

</details>

#### reports parse errors

1. expect error contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "Parse error in module.spl:10"
expect error.contains("Parse error")
```

</details>

#### continues on non-fatal errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val continue_on_error = true
expect continue_on_error == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
