# RTL MDSOC Plug-In Stubs Specification

> Verifies that the 4 MDSOC plug-in stub files exist with the correct structure:

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
| Updated | 2026-08-26 |
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

- AC-5: vhdl_emit_fp_stub.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_fp_stub.spl exists")
val path = stub_fp_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl contains function vhdl_emit_fp_op_stub

- AC-5: vhdl_emit_fp_stub.spl contains function vhdl_emit_fp_op_stub
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_fp_stub.spl contains function vhdl_emit_fp_op_stub")
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_fp_op_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl TODO references Feature A

- AC-5: vhdl_emit_fp_stub.spl TODO references Feature A
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_fp_stub.spl TODO references Feature A")
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature A")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_fp_stub.spl has capsule marker vhdl.emit.data.fp

- AC-5: vhdl_emit_fp_stub.spl has capsule marker vhdl.emit.data.fp
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_fp_stub.spl has capsule marker vhdl.emit.data.fp")
val path = stub_fp_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.data.fp")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.data.simd (AC-5)

#### AC-5: vhdl_emit_simd_stub.spl exists

- AC-5: vhdl_emit_simd_stub.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_simd_stub.spl exists")
val path = stub_simd_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl contains function vhdl_emit_simd_op_stub

- AC-5: vhdl_emit_simd_stub.spl contains function vhdl_emit_simd_op_stub
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_simd_stub.spl contains function vhdl_emit_simd_op_stub")
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_simd_op_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl TODO references Feature A

- AC-5: vhdl_emit_simd_stub.spl TODO references Feature A
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_simd_stub.spl TODO references Feature A")
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature A")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl has capsule marker vhdl.emit.data.simd

- AC-5: vhdl_emit_simd_stub.spl has capsule marker vhdl.emit.data.simd
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_simd_stub.spl has capsule marker vhdl.emit.data.simd")
val path = stub_simd_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.data.simd")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.state.cache (AC-5)

#### AC-5: vhdl_emit_cache_stub.spl exists

- AC-5: vhdl_emit_cache_stub.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_cache_stub.spl exists")
val path = stub_cache_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl contains function vhdl_emit_cache_state_stub

- AC-5: vhdl_emit_cache_stub.spl contains function vhdl_emit_cache_state_stub
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_cache_stub.spl contains function vhdl_emit_cache_state_stub")
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_cache_state_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl TODO references Feature B

- AC-5: vhdl_emit_cache_stub.spl TODO references Feature B
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_cache_stub.spl TODO references Feature B")
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature B")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl has capsule marker vhdl.emit.state.cache

- AC-5: vhdl_emit_cache_stub.spl has capsule marker vhdl.emit.state.cache
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_cache_stub.spl has capsule marker vhdl.emit.state.cache")
val path = stub_cache_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.state.cache")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: vhdl.emit.state.hart (AC-5)

#### AC-5: vhdl_emit_hart_stub.spl exists

- AC-5: vhdl_emit_hart_stub.spl exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_hart_stub.spl exists")
val path = stub_hart_path()
val exists = rt_file_exists(path)
check_msg(exists, "stub file not found (SA-4 not run yet): " + path)
expect(exists).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl contains function vhdl_emit_hart_state_stub

- AC-5: vhdl_emit_hart_stub.spl contains function vhdl_emit_hart_state_stub
   - Expected: has_fn is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_hart_stub.spl contains function vhdl_emit_hart_state_stub")
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_fn = content.contains("fn vhdl_emit_hart_state_stub")
expect(has_fn).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl TODO references Feature B

- AC-5: vhdl_emit_hart_stub.spl TODO references Feature B
   - Expected: has_todo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_hart_stub.spl TODO references Feature B")
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_todo = content.contains("Feature B")
expect(has_todo).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl has capsule marker vhdl.emit.state.hart

- AC-5: vhdl_emit_hart_stub.spl has capsule marker vhdl.emit.state.hart
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_hart_stub.spl has capsule marker vhdl.emit.state.hart")
val path = stub_hart_path()
check_msg(rt_file_exists(path), "stub not found: " + path)
val content = read_file(path)
val has_marker = content.contains("# capsule: vhdl.emit.state.hart")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Plug-In Stubs: re-export facade inclusion (AC-5)

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_fp_stub

- AC-5: vhdl/__init__.spl re-exports vhdl_emit_fp_stub
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl/__init__.spl re-exports vhdl_emit_fp_stub")
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_fp_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_simd_stub

- AC-5: vhdl/__init__.spl re-exports vhdl_emit_simd_stub
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl/__init__.spl re-exports vhdl_emit_simd_stub")
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_simd_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_cache_stub

- AC-5: vhdl/__init__.spl re-exports vhdl_emit_cache_stub
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl/__init__.spl re-exports vhdl_emit_cache_stub")
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val content = read_file(path)
val has_reexport = content.contains("vhdl_emit_cache_stub")
expect(has_reexport).to_equal(true)
```

</details>

#### AC-5: vhdl/__init__.spl re-exports vhdl_emit_hart_stub

- AC-5: vhdl/__init__.spl re-exports vhdl_emit_hart_stub
   - Expected: has_reexport is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl/__init__.spl re-exports vhdl_emit_hart_stub")
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

- **Requirements:** `doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md`
- **Design:** `doc/05_design/rtl_riscv_mdsoc_capsules.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3542c0b3929242bd2d030bc6ddcff43d9c7493f956ee708910bb6b5d3ee0b65c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3542c0b3929242bd2d030bc6ddcff43d9c7493f956ee708910bb6b5d3ee0b65c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3542c0b3929242bd2d030bc6ddcff43d9c7493f956ee708910bb6b5d3ee0b65c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl
mirror: doc/06_spec/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: vhdl_emit_fp_stub.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: vhdl_emit_fp_stub.spl contains function vhdl_emit_fp_op_stub' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: vhdl_emit_fp_stub.spl TODO references Feature A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
