# Loader Exec Memory Specification

> <details>

<!-- sdn-diagram:id=loader_exec_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loader_exec_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loader_exec_memory_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loader_exec_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader Exec Memory Specification

## Scenarios

### Exec memory mapping

#### x86_64 only

#### skips on non-x86_64 hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### maps executable memory and runs a tiny function

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Machine code: mov eax, 42; ret
val code: [u8] = [184, 42, 0, 0, 0, 195]

val addr = native_alloc_exec_memory(code.len() as i64)
expect(addr > 0)

val written = native_write_exec_memory(addr, code, 0)
expect(written).to_equal(code.len() as i64)

val made_exec = native_make_executable(addr, code.len() as i64)
expect(made_exec)

val result = native_call_function_0(addr)
expect(result).to_equal(42)

val freed = native_free_exec_memory(addr, code.len() as i64)
expect(freed)
```

</details>

#### fails gracefully on oversized allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val huge_size = 1_099_511_627_776i64  # 1 TB
val addr = native_alloc_exec_memory(huge_size)
expect(addr).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/loader_exec_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Exec memory mapping

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
