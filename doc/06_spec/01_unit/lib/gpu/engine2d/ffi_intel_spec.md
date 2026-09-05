# ffi_intel_spec

> Intel oneAPI Level Zero FFI Dispatch Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ffi_intel_spec

Intel oneAPI Level Zero FFI Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Intel oneAPI Level Zero FFI Dispatch Specification

@tag: gpu, engine2d, intel, oneapi, level_zero, ffi
NO COVERAGE CLAIMED. Stream F4 (2026-08-09) removed the
`@cover src/lib/gc_async_mut/gpu/engine2d/ffi_intel.spl 80%` claim that stood here: all 11 `it` bodies are the single gate assertion and the file never
references IntelDynFfi. Worse, the named subject is a 3-line facade whose
re-export target does not exist on disk, so nothing could cover it at all.
The real IntelDynFfi is src/lib/nogc_sync_mut/gpu/engine2d/ffi_intel.spl.
Not rewritten as a real test: this host has no Intel GPU / Level Zero
runtime, so only the constructor-rejection cases would be meaningful.
See doc/08_tracking/bug/gated_specs_are_tautology_shells_2026-08-09.md
and doc/08_tracking/bug/gc_async_mut_gpu_ffi_facades_are_dangling_2026-08-09.md.

Verifies IntelDynFfi dispatch class: dynamic-first (DynLib dlopen libze_loader.so)
since no Rust runtime exists for rt_intel_*. Covers AC-4 + AC-8.

## Scenarios

### IntelDynFfi

### create_dynamic

#### AC-4: attempts to load libze_loader.so

- AC-4: attempts to load libze_loader.so
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: attempts to load libze_loader.so")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: returns nil when Level Zero not installed

- AC-8: returns nil when Level Zero not installed
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: returns nil when Level Zero not installed")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### create_static

#### AC-8: static mode available when runtime is built

- AC-8: static mode available when runtime is built
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: static mode available when runtime is built")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero driver

#### AC-4: zeInit returns success

- AC-4: zeInit returns success
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: zeInit returns success")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: zeDriverGet returns driver count

- AC-4: zeDriverGet returns driver count
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: zeDriverGet returns driver count")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero device

#### AC-4: device enumeration for Arc/Xe/integrated

- AC-4: device enumeration for Arc/Xe/integrated
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: device enumeration for Arc/Xe/integrated")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero command list

#### AC-4: zeCommandListCreate returns handle

- AC-4: zeCommandListCreate returns handle
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: zeCommandListCreate returns handle")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### Level Zero kernel

#### AC-4: zeKernelCreate from SPIR-V module

- AC-4: zeKernelCreate from SPIR-V module
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: zeKernelCreate from SPIR-V module")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: zeCommandListAppendLaunchKernel dispatches

- AC-4: zeCommandListAppendLaunchKernel dispatches
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: zeCommandListAppendLaunchKernel dispatches")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### platform support

#### AC-7: Intel L0 on Linux and Windows

- AC-7: Intel L0 on Linux and Windows
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-7: Intel L0 on Linux and Windows")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: Intel dynamic-only (no Rust runtime)

- AC-4: Intel dynamic-only (no Rust runtime)
   - Expected: test_env_require("SIMPLE_GPU_TEST") equals `blocked:SIMPLE_GPU_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: Intel dynamic-only (no Rust runtime)")
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

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

- Canonical SPipe generation for source `214734362526db47e67f552d934a1eb946e359e12dfbc53f1aa0ff5010299d90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `214734362526db47e67f552d934a1eb946e359e12dfbc53f1aa0ff5010299d90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `214734362526db47e67f552d934a1eb946e359e12dfbc53f1aa0ff5010299d90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_intel_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_intel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_intel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: attempts to load libze_loader.so' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: returns nil when Level Zero not installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_intel_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: static mode available when runtime is built' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
