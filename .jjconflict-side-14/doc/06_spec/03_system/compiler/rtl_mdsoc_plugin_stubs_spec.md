# RTL MDSOC Plug-In Stubs Specification

> Verifies that the 4 MDSOC plug-in stub files exist with the correct structure:

<!-- sdn-diagram:id=rtl_mdsoc_plugin_stubs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rtl_mdsoc_plugin_stubs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rtl_mdsoc_plugin_stubs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rtl_mdsoc_plugin_stubs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTL MDSOC Plug-In Stubs Specification

Verifies that the 4 MDSOC plug-in stub files exist with the correct structure:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Source | `test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the 4 MDSOC plug-in stub files exist with the correct structure:
- Each stub file exists at the designated path
- Each stub contains a function with the expected name
- Each function contains a TODO link referencing Feature A or Feature B
- Each stub file has the correct capsule marker

## Plug-In Stub Shape (AC-5)

Each stub is a one-function module:
- `vhdl_emit_fp_stub.spl`    → `fn vhdl_emit_fp_op_stub`    → TODO Feature A
- `vhdl_emit_simd_stub.spl`  → `fn vhdl_emit_simd_op_stub`  → TODO Feature A
- `vhdl_emit_cache_stub.spl` → `fn vhdl_emit_cache_state_stub` → TODO Feature B
- `vhdl_emit_hart_stub.spl`  → `fn vhdl_emit_hart_state_stub`  → TODO Feature B

TDD-red: these files do not exist before Phase 5 SA-4 runs.

## Acceptance Criteria

- AC-5: Capsule plug-in points named for SIMD/FP RTL hooks and SMP/cache RTL hooks;
  capsules can be empty stubs with TODO links to Feature A / Feature B

## Scenarios

### RTL MDSOC Plug-In Stubs: vhdl.emit.data.fp (AC-5)

#### AC-5: vhdl_emit_fp_stub.spl exists

1. check msg
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_fp_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl contains function vhdl_emit_fp_op_stub

1. check msg
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_fp_op_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl TODO references Feature A

1. check msg
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature A")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl has capsule marker vhdl.emit.data.fp

1. check msg
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.data.fp")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.data.simd (AC-5)

#### AC-5: vhdl_emit_simd_stub.spl exists

1. check msg
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_simd_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl contains function vhdl_emit_simd_op_stub

1. check msg
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_simd_op_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl TODO references Feature A

1. check msg
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature A")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl has capsule marker vhdl.emit.data.simd

1. check msg
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.data.simd")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.state.cache (AC-5)

#### AC-5: vhdl_emit_cache_stub.spl exists

1. check msg
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_cache_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl contains function vhdl_emit_cache_state_stub

1. check msg
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_cache_state_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl TODO references Feature B

1. check msg
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature B")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl has capsule marker vhdl.emit.state.cache

1. check msg
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.state.cache")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.state.hart (AC-5)

#### AC-5: vhdl_emit_hart_stub.spl exists

1. check msg
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_hart_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl contains function vhdl_emit_hart_state_stub

1. check msg
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_hart_state_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl TODO references Feature B

1. check msg
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature B")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl has capsule marker vhdl.emit.state.hart

1. check msg
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.state.hart")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: re-export facade inclusion (AC-5)

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_fp_stub

1. check msg
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_fp_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_simd_stub

1. check msg
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_simd_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_cache_stub

1. check msg
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_cache_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_hart_stub

1. check msg
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_hart_stub")
expect(has_reexport).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md](doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md)
- **Design:** [doc/05_design/rtl_riscv_mdsoc_capsules.md](doc/05_design/rtl_riscv_mdsoc_capsules.md)


</details>
