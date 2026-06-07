# Gc Dyn Ffi Specification

> <details>

<!-- sdn-diagram:id=gc_dyn_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_dyn_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_dyn_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_dyn_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Dyn Ffi Specification

## Scenarios

### DynLoader FFI Pattern

### Stateless wrapper

#### DynLoader has no owns_handle field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dl = MockDynLoader.instance()
expect(dl.lib_path).to_equal("libspl_torch.so")
# No owns_handle field — stateless
```

</details>

#### each call creates fresh loader instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dl1 = mock_dl()
val dl2 = mock_dl()
expect(dl1.lib_path).to_equal(dl2.lib_path)
```

</details>

### Function dispatch

#### call0 dispatches without args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mock_dyn_torch_available()
expect(result).to_equal(true)
```

</details>

#### call1 dispatches with one arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mock_dyn_torch_tensor_neg(10)
expect(result).to_equal(11)
```

</details>

### Migration safety

#### no ownership state means zero-change migration

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dyn_ffi.spl has no owns_handle, no drop(), no GC interaction
# Safe to copy to nogc_sync_mut/ without modification
val dl = MockDynLoader.instance()
# Verify no state to manage
expect(dl.lib_path.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch/gc_dyn_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DynLoader FFI Pattern
- Stateless wrapper
- Function dispatch
- Migration safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
