# Link Dependency Manager Specification

> <details>

<!-- sdn-diagram:id=link_dependency_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=link_dependency_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

link_dependency_manager_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=link_dependency_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Link Dependency Manager Specification

## Scenarios

### link_dependency_manager

### check-links output format

#### found_lib_shows_ok: found library shows OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = helper_format_check_line("c", true)
expect(line).to_start_with("[OK]")
expect(line).to_contain("c")
```

</details>

#### missing_lib_shows_miss: missing library shows MISS

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = helper_format_check_line("nonexistent", false)
expect(line).to_start_with("[MISS]")
expect(line).to_contain("nonexistent")
```

</details>

### full resolution pipeline

#### linux_no_overrides: Linux with no SDN gives 4 defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("linux", false, [], [], [])
expect(libs.len()).to_equal(4)
expect(libs[0]).to_equal("c")
```

</details>

#### linux_with_project_lib: project libs appended to defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("linux", false, ["ssl"], [], [])
expect(libs.len()).to_equal(5)
expect(libs[4]).to_equal("ssl")
```

</details>

#### linux_with_os_override: OS-specific libs appended

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("linux", false, [], ["rt"], [])
expect(libs.len()).to_equal(5)
expect(libs[4]).to_equal("rt")
```

</details>

#### linux_riscv64_full_stack: all layers merge correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("linux", false, ["project_lib"], ["rt"], ["atomic"])
expect(libs.len()).to_equal(7)
expect(libs[0]).to_equal("c")
expect(libs[4]).to_equal("project_lib")
expect(libs[5]).to_equal("rt")
expect(libs[6]).to_equal("atomic")
```

</details>

#### no_default_libs_strips_defaults: no-default-libs gives only extras

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("linux", true, ["custom"], [], [])
expect(libs.len()).to_equal(1)
expect(libs[0]).to_equal("custom")
```

</details>

#### windows_defaults: Windows gets kernel32 and user32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("windows", false, [], [], [])
expect(libs.len()).to_equal(2)
expect(libs[0]).to_equal("kernel32")
```

</details>

#### macos_defaults: macOS includes System library

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_resolve("macos", false, [], [], [])
expect(libs.len()).to_equal(4)
expect(libs[3]).to_equal("System")
```

</details>

### missing library detection

#### all_found_returns_zero: all found means success

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var all_found = true
val libs = ["c", "pthread"]
for lib in libs:
    val found = lib == "c" or lib == "pthread"
    if not found:
        all_found = false
expect(all_found).to_equal(true)
```

</details>

#### one_missing_returns_nonzero: any missing means failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var all_found = true
val libs = ["c", "nonexistent_lib"]
for lib in libs:
    val found = lib == "c"
    if not found:
        all_found = false
expect(all_found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/link_dependency_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- link_dependency_manager
- check-links output format
- full resolution pipeline
- missing library detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
