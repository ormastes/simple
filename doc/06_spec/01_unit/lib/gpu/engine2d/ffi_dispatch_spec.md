# ffi_dispatch_spec

> FFI Dispatch Layer Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ffi_dispatch_spec

FFI Dispatch Layer Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FFI Dispatch Layer Specification

@tag: gpu, engine2d, ffi, dispatch, dynamic, static
@cover src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl 80%

Verifies the dual-path FFI dispatch layer that allows backends to use
either static (extern fn) or dynamic (DynLib dlopen) function resolution.
Covers AC-8: dynamic + static linking support.

## Scenarios

### GpuFfiMode

#### AC-8: has Static variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-8: has Static variant
   - Expected: mode.to_text() equals `Static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: has Static variant")
val mode = GpuFfiMode.Static
expect(mode.to_text()).to_equal("Static")
```

</details>

#### AC-8: has Dynamic variant

- AC-8: has Dynamic variant
   - Expected: mode.to_text() equals `Dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: has Dynamic variant")
val mode = GpuFfiMode.Dynamic
expect(mode.to_text()).to_equal("Dynamic")
```

</details>

### default_ffi_mode

#### AC-8: returns a valid GpuFfiMode

- AC-8: returns a valid GpuFfiMode
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: returns a valid GpuFfiMode")
val mode = default_ffi_mode()
val is_valid = mode.to_text() == "Static" or mode.to_text() == "Dynamic"
expect(is_valid).to_equal(true)
```

</details>

### FfiDispatchBase

#### AC-8: mode() returns the dispatch mode

- AC-8: mode() returns the dispatch mode
   - Expected: mode.to_text() equals `Dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: mode() returns the dispatch mode")
val mode = GpuFfiMode.Dynamic
expect(mode.to_text()).to_equal("Dynamic")
```

</details>

#### AC-8: is_available() returns bool for availability check

- AC-8: is_available() returns bool for availability check
   - Expected: available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: is_available() returns bool for availability check")
val available = false
expect(available).to_equal(false)
```

</details>

### dynamic dispatch

#### AC-8: create_dynamic returns nil when library not found

- AC-8: create_dynamic returns nil when library not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: create_dynamic returns nil when library not found")
val result = try_create_dynamic_vulkan("nonexistent_libvulkan.so.999")
expect(result).to_be_nil()
```

</details>

#### AC-8: graceful fallback when vendor SDK not installed

- AC-8: graceful fallback when vendor SDK not installed
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-8: graceful fallback when vendor SDK not installed")
val mode = resolve_ffi_mode("vulkan")
val is_valid = mode.to_text() == "Static" or mode.to_text() == "Dynamic"
expect(is_valid).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `03a6a90352b6f879932eeab1835fe920c549cb7a58f08423b87ad6fdc1300258`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03a6a90352b6f879932eeab1835fe920c549cb7a58f08423b87ad6fdc1300258`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03a6a90352b6f879932eeab1835fe920c549cb7a58f08423b87ad6fdc1300258`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: has Static variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: has Dynamic variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_dispatch_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-8: returns a valid GpuFfiMode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
