# Bootstrap Ffi Specification

> <details>

<!-- sdn-diagram:id=bootstrap_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Ffi Specification

## Scenarios

### Bootstrap Ffi

#### exposes runtime file existence checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("test/unit/compiler/loader/bootstrap_ffi_spec.spl")).to_equal(true)
expect(rt_file_exists("test/unit/compiler/loader/not_real.spl")).to_equal(false)
```

</details>

#### reads text through runtime file FFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("test/unit/compiler/loader/bootstrap_ffi_spec.spl")
expect(content.len()).to_be_greater_than(0)
expect(content).to_contain("Bootstrap Ffi")
```

</details>

#### hashes files through runtime crypto FFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hash = rt_file_hash_sha256("test/unit/compiler/loader/bootstrap_ffi_spec.spl")
expect(hash.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/bootstrap_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bootstrap Ffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
