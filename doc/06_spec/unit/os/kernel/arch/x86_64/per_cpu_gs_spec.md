# Per Cpu Gs Specification

> Tests covering x86_64 Per-CPU GS_BASE Register Convention, GS_BASE write at boot — baremetal path, GS_BASE NOT written in hosted (non-baremetal) build, x86_64 Per-CPU FS_BASE Register Convention, FS_BASE write at boot — baremetal path, FS_BASE NOT written in hosted (non-baremetal) build, GS and FS are independent state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Cpu Gs Specification

## Scenarios

### x86_64 Per-CPU GS_BASE Register Convention

### GS_BASE write at boot — baremetal path

#### GS_BASE is set to per_cpu_base for cpu 0 (shift has no effect)

- GS_BASE is set to per_cpu_base for cpu 0 (shift has no effect)
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GS_BASE is set to per_cpu_base for cpu 0 (shift has no effect)")
val cpu_id = 0u32
val per_cpu_base = 0xFFFF800000100000u64
val per_cpu_shift = 12u32
simulate_gs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val gs = read_gs_base_test()
val expected = per_cpu_base + (0u64 << per_cpu_shift)
expect(gs).to_equal(expected)
```

</details>

#### GS_BASE is set correctly for cpu 1 (one slot up)

- GS_BASE is set correctly for cpu 1 (one slot up)
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GS_BASE is set correctly for cpu 1 (one slot up)")
val cpu_id = 1u32
val per_cpu_base = 0xFFFF800000100000u64
val per_cpu_shift = 12u32
simulate_gs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val gs = read_gs_base_test()
val expected = per_cpu_base + (1u64 << per_cpu_shift)
expect(gs).to_equal(expected)
```

</details>

#### GS_BASE differs across cpu IDs (no aliasing)

- GS_BASE differs across cpu IDs (no aliasing)
   - Expected: gs_cpu0 equals `base`
   - Expected: gs_cpu1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GS_BASE differs across cpu IDs (no aliasing)")
val base = 0xFFFF800000100000u64
val shift = 12u32
simulate_gs_write_baremetal(0u32, base, shift)
val gs_cpu0 = read_gs_base_test()
simulate_gs_write_baremetal(1u32, base, shift)
val gs_cpu1 = read_gs_base_test()
expect(gs_cpu0).to_equal(base)
expect(gs_cpu1).to_equal(base + 4096u64)
```

</details>

#### GS_BASE uses the per_cpu_shift for slot sizing

- GS_BASE uses the per_cpu_shift for slot sizing
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GS_BASE uses the per_cpu_shift for slot sizing")
val base = 0xFFFF800000200000u64
val shift = 16u32
simulate_gs_write_baremetal(2u32, base, shift)
val gs = read_gs_base_test()
val expected = base + (2u64 << shift)
expect(gs).to_equal(expected)
```

</details>

### GS_BASE NOT written in hosted (non-baremetal) build

#### simulate_gs_write_hosted does NOT modify GS_BASE

- simulate_gs_write_hosted does NOT modify GS_BASE
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simulate_gs_write_hosted does NOT modify GS_BASE")
val per_cpu_base = 0xFFFF800000300000u64
simulate_gs_write_baremetal(0u32, per_cpu_base, 12u32)
val before = read_gs_base_test()
simulate_gs_write_hosted()
val after = read_gs_base_test()
expect(after).to_equal(before)
```

</details>

### x86_64 Per-CPU FS_BASE Register Convention

### FS_BASE write at boot — baremetal path

#### FS_BASE is set to per_cpu_base for cpu 0

- FS_BASE is set to per_cpu_base for cpu 0
   - Expected: fs equals `per_cpu_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FS_BASE is set to per_cpu_base for cpu 0")
val cpu_id = 0u32
val per_cpu_base = 0xFFFF800000400000u64
val per_cpu_shift = 12u32
simulate_fs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val fs = read_fs_base_test()
expect(fs).to_equal(per_cpu_base)
```

</details>

#### FS_BASE is set correctly for cpu 1

- FS_BASE is set correctly for cpu 1
   - Expected: fs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FS_BASE is set correctly for cpu 1")
val cpu_id = 1u32
val per_cpu_base = 0xFFFF800000400000u64
val per_cpu_shift = 12u32
simulate_fs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val fs = read_fs_base_test()
val expected = per_cpu_base + 4096u64
expect(fs).to_equal(expected)
```

</details>

#### FS_BASE differs across cpu IDs (no aliasing)

- FS_BASE differs across cpu IDs (no aliasing)
   - Expected: fs_cpu0 equals `base`
   - Expected: fs_cpu1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FS_BASE differs across cpu IDs (no aliasing)")
val base = 0xFFFF800000400000u64
val shift = 12u32
simulate_fs_write_baremetal(0u32, base, shift)
val fs_cpu0 = read_fs_base_test()
simulate_fs_write_baremetal(1u32, base, shift)
val fs_cpu1 = read_fs_base_test()
expect(fs_cpu0).to_equal(base)
expect(fs_cpu1).to_equal(base + 4096u64)
```

</details>

### FS_BASE NOT written in hosted (non-baremetal) build

#### simulate_fs_write_hosted does NOT modify FS_BASE

- simulate_fs_write_hosted does NOT modify FS_BASE
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simulate_fs_write_hosted does NOT modify FS_BASE")
val per_cpu_base = 0xFFFF800000500000u64
simulate_fs_write_baremetal(0u32, per_cpu_base, 12u32)
val before = read_fs_base_test()
simulate_fs_write_hosted()
val after = read_fs_base_test()
expect(after).to_equal(before)
```

</details>

### GS and FS are independent state

#### writing GS does not affect FS

- writing GS does not affect FS
   - Expected: fs_before equals `fs_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writing GS does not affect FS")
val gs_base = 0xFFFF800000600000u64
val fs_base = 0xFFFF800000700000u64
simulate_fs_write_baremetal(0u32, fs_base, 12u32)
val fs_before = read_fs_base_test()
simulate_gs_write_baremetal(3u32, gs_base, 12u32)
val fs_after = read_fs_base_test()
expect(fs_before).to_equal(fs_after)
```

</details>

#### writing FS does not affect GS

- writing FS does not affect GS
   - Expected: gs_before equals `gs_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writing FS does not affect GS")
val gs_base = 0xFFFF800000800000u64
val fs_base = 0xFFFF800000900000u64
simulate_gs_write_baremetal(0u32, gs_base, 12u32)
val gs_before = read_gs_base_test()
simulate_fs_write_baremetal(3u32, fs_base, 12u32)
val gs_after = read_gs_base_test()
expect(gs_before).to_equal(gs_after)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 Per-CPU GS_BASE Register Convention, GS_BASE write at boot — baremetal path, GS_BASE NOT written in hosted (non-baremetal) build, x86_64 Per-CPU FS_BASE Register Convention, FS_BASE write at boot — baremetal path, FS_BASE NOT written in hosted (non-baremetal) build, GS and FS are independent state.
- x86_64 Per-CPU GS_BASE Register Convention
- GS_BASE write at boot — baremetal path
- GS_BASE NOT written in hosted (non-baremetal) build
- x86_64 Per-CPU FS_BASE Register Convention
- FS_BASE write at boot — baremetal path
- FS_BASE NOT written in hosted (non-baremetal) build
- GS and FS are independent state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `246d8d2d9709e84fe21265d2041e2511fe2085711a9fa837425ec4c27219e1cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `246d8d2d9709e84fe21265d2041e2511fe2085711a9fa837425ec4c27219e1cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `246d8d2d9709e84fe21265d2041e2511fe2085711a9fa837425ec4c27219e1cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GS_BASE is set to per_cpu_base for cpu 0 (shift has no effect)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GS_BASE is set correctly for cpu 1 (one slot up)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GS_BASE differs across cpu IDs (no aliasing)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
