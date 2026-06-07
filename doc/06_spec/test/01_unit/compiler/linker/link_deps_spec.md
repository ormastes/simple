# Link Deps Specification

> <details>

<!-- sdn-diagram:id=link_deps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=link_deps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

link_deps_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=link_deps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Link Deps Specification

## Scenarios

### link_deps

### default resolution

#### linux_defaults: Linux defaults include c, pthread, dl, m

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val libs = helper_default_linux_libs()
expect(libs.len()).to_equal(4)
expect(libs[0]).to_equal("c")
expect(libs[3]).to_equal("m")
```

</details>

#### default_lib_dirs: defaults include simple lib dirs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = helper_default_lib_dirs()
expect(dirs.len()).to_equal(2)
expect(dirs[0]).to_equal("/usr/lib/simple")
```

</details>

### SDN merge

#### merge_empty_extras: merging with empty extras returns defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_merge_lists(helper_default_linux_libs(), [])
expect(result.len()).to_equal(4)
expect(result[0]).to_equal("c")
```

</details>

#### merge_adds_extra_libs: extra libs are appended

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_merge_lists(helper_default_linux_libs(), ["extra_lib"])
expect(result.len()).to_equal(5)
expect(result[4]).to_equal("extra_lib")
```

</details>

#### merge_multiple_extras: multiple extras all appended

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_merge_lists(helper_default_linux_libs(), ["rt", "util"])
expect(result.len()).to_equal(6)
expect(result[4]).to_equal("rt")
expect(result[5]).to_equal("util")
```

</details>

#### merge_trims_whitespace: whitespace in extras is trimmed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_merge_lists([], [" foo ", " bar "])
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("foo")
expect(result[1]).to_equal("bar")
```

</details>

#### merge_skips_empty: empty strings in extras are skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_merge_lists([], ["", "valid", ""])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("valid")
```

</details>

### no-default-libs

#### no_default_includes_only_extras: no-default-libs skips defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_resolve_no_default_libs(true, helper_default_linux_libs(), ["custom_lib"])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("custom_lib")
```

</details>

#### no_default_empty_when_no_extras: no-default-libs with no extras gives empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_resolve_no_default_libs(true, helper_default_linux_libs(), [])
expect(result.len()).to_equal(0)
```

</details>

#### with_default_includes_both: with defaults, both are included

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_resolve_no_default_libs(false, helper_default_linux_libs(), ["extra"])
expect(result.len()).to_equal(5)
expect(result[0]).to_equal("c")
expect(result[4]).to_equal("extra")
```

</details>

### platform/arch overrides

#### multi_layer_merge: base + os + arch layers all merge

1. var libs = helper default linux libs
2. libs = helper merge lists
3. libs = helper merge lists
4. libs = helper merge lists
   - Expected: libs.len() equals `7`
   - Expected: libs[4] equals `project_lib`
   - Expected: libs[5] equals `rt`
   - Expected: libs[6] equals `atomic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates: defaults + [links] + [links.linux] + [links.linux.riscv64]
var libs = helper_default_linux_libs()
libs = helper_merge_lists(libs, ["project_lib"])
libs = helper_merge_lists(libs, ["rt"])
libs = helper_merge_lists(libs, ["atomic"])
expect(libs.len()).to_equal(7)
expect(libs[4]).to_equal("project_lib")
expect(libs[5]).to_equal("rt")
expect(libs[6]).to_equal("atomic")
```

</details>

### CSV parsing

#### parse_csv_single: single value parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_parse_csv("foo")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("foo")
```

</details>

#### parse_csv_multiple: comma-separated values parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_parse_csv("foo, bar, baz")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("foo")
expect(result[1]).to_equal("bar")
expect(result[2]).to_equal("baz")
```

</details>

#### parse_csv_empty: empty string gives empty result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = helper_parse_csv("")
expect(result.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/link_deps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- link_deps
- default resolution
- SDN merge
- no-default-libs
- platform/arch overrides
- CSV parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
