# SmfSource Specification

> Tests for the SmfSource enum — unified abstraction for file-backed and in-memory SMF modules.

<!-- sdn-diagram:id=smf_source_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_source_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_source_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_source_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SmfSource Specification

Tests for the SmfSource enum — unified abstraction for file-backed and in-memory SMF modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SMF-009 |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | In Progress |
| Plan | doc/03_plan/smf_load_enable_plan.md |
| Source | `test/01_unit/compiler/interpreter/smf_source_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the SmfSource enum — unified abstraction for file-backed
and in-memory SMF modules.

## Scenarios

### SmfSource

#### creates file source and reports name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SmfSource.FileSmf(path: "/cache/mod.smf")
expect(smf_source_get_name(src)).to_equal("/cache/mod.smf")
```

</details>

#### creates memory source and reports name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0, 1, 2, 3]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "std.text")
expect(smf_source_get_name(src)).to_equal("std.text")
```

</details>

#### identifies file source correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SmfSource.FileSmf(path: "/a.smf")
expect(smf_source_is_file(src)).to_equal(true)
expect(smf_source_is_memory(src)).to_equal(false)
```

</details>

#### identifies memory source correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "m")
expect(smf_source_is_file(src)).to_equal(false)
expect(smf_source_is_memory(src)).to_equal(true)
```

</details>

#### returns file path for file source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SmfSource.FileSmf(path: "/cache/x.smf")
expect(smf_source_file_path(src)).to_equal("/cache/x.smf")
```

</details>

#### returns empty path for memory source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "m")
expect(smf_source_file_path(src)).to_equal("")
```

</details>

#### describes file source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SmfSource.FileSmf(path: "/a.smf")
expect(smf_source_describe(src)).to_start_with("file:")
```

</details>

#### describes memory source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "mod")
expect(smf_source_describe(src)).to_start_with("memory:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/smf_load_enable_plan.md](doc/03_plan/smf_load_enable_plan.md)


</details>
