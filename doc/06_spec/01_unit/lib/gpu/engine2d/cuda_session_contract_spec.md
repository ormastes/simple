# cuda_session_contract_spec

> Purpose: Prove that CudaSession compute contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_session_contract_spec

Purpose: Prove that CudaSession compute contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CudaSession compute contract.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CudaSession compute contract

#### reports CUDA kind and availability without initializing hardware

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports CUDA kind and availability without initializing hardware
- Verify: reports CUDA kind and availability without initializing hardware
   - Expected: session.kind() equals `BackendSessionKind.Cuda`
   - Expected: session.is_available() equals `cuda_available()`
   - Expected: session.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports CUDA kind and availability without initializing hardware")
step("Verify: reports CUDA kind and availability without initializing hardware")
# @req: REQ-LIB-GPU-001
val session = CudaSession.create()

expect(session.kind()).to_equal(BackendSessionKind.Cuda)
expect(session.is_available()).to_equal(cuda_available())
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when launching without a loaded module

- fails closed when launching without a loaded module
- Verify: fails closed when launching without a loaded module
   - Expected: session.launch_kernel("kernel_clear", 1, 1, 1, 1) equals `1`
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096) equals `1`
   - Expected: session.fill_kernel(64, 64, 4096) equals `1`
   - Expected: session.copy_kernel(64, 64, 4096) equals `1`
   - Expected: session.alpha_blend_kernel(64, 64, 4096) equals `1`
   - Expected: session.scroll_kernel(64, 64, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when launching without a loaded module")
step("Verify: fails closed when launching without a loaded module")
val session = CudaSession.create()

expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### fails generated 2D launches closed for invalid argument buffers

- fails generated 2D launches closed for invalid argument buffers
- Verify: fails generated 2D launches closed for invalid argument buffers
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0) equals `1`
   - Expected: session.fill_kernel(64, 64, 0) equals `1`
   - Expected: session.fill_kernel(0, 64, 4096) equals `1`
   - Expected: session.launch_generated_2d("unsupported", 64, 64, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails generated 2D launches closed for invalid argument buffers")
step("Verify: fails generated 2D launches closed for invalid argument buffers")
var session = CudaSession.create()
session.module_cache = 1234

expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(1)
expect(session.fill_kernel(64, 64, 0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.fill_kernel(0, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.launch_generated_2d("unsupported", 64, 64, 4096)).to_equal(1)
```

</details>

#### supports injected CUDA FFI for the shared backend interface

- supports injected CUDA FFI for the shared backend interface
- Verify: supports injected CUDA FFI for the shared backend interface
   - Expected: session.kind() equals `BackendSessionKind.Cuda`
   - Expected: session.alloc(0) equals `0`
   - Expected: session.launch_kernel("kernel_clear", 1, 1, 1, 1) equals `1`
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0) equals `1`
   - Expected: session.synchronize() equals `1`
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports injected CUDA FFI for the shared backend interface")
step("Verify: supports injected CUDA FFI for the shared backend interface")
var session = CudaSession.create_with_ffi(CudaFfi.create_static())

expect(session.kind()).to_equal(BackendSessionKind.Cuda)
expect(session.alloc(0)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 0)).to_equal(1)
expect(session.synchronize()).to_equal(1)  # oracle: 1 — named expected value from the requirement
session.shutdown()
expect(session.ref_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### quarantines a shared context after completion becomes unknown

- quarantines a shared context after completion becomes unknown
- Verify: quarantines a shared context after completion becomes unknown
   - Expected: session.completion_unknown is true
   - Expected: session.is_valid() is false
   - Expected: session.init() equals `1`
   - Expected: session.alloc(4) equals `0`
   - Expected: session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("quarantines a shared context after completion becomes unknown")
step("Verify: quarantines a shared context after completion becomes unknown")
var session = CudaSession.create()
session.is_initialized = true
session.ctx = 7
session.module_cache = 11

session.quarantine_completion_unknown()

expect(session.completion_unknown).to_equal(true)
expect(session.is_valid()).to_equal(false)
expect(session.init()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.alloc(4)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(session.launch_kernel_args("kernel_clear", 1, 1, 1, 1, 1, 1, 4096)).to_equal(1)
session.free(4096)
session.ctx = 0
session.module_cache = 0
session.shutdown()
```

</details>

#### reports shared generated 2D runtime provenance without hardware

- reports shared generated 2D runtime provenance without hardware
- Verify: reports shared generated 2D runtime provenance without hardware
   - Expected: missing_runtime.ready is false
   - Expected: missing_runtime.typed_status equals `cuda-runtime-unavailable`
   - Expected: missing_module.typed_status equals `cuda-module-unavailable`
   - Expected: missing_args.typed_status equals `args-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports shared generated 2D runtime provenance without hardware")
step("Verify: reports shared generated 2D runtime provenance without hardware")
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_FILL, 64, 64, 0)

expect(missing_runtime.ready).to_equal(false)
expect(missing_runtime.typed_status).to_equal("cuda-runtime-unavailable")
expect(missing_module.typed_status).to_equal("cuda-module-unavailable")
expect(missing_args.typed_status).to_equal("args-unavailable")
expect(missing_args.diagnostic_text()).to_contain("launch=cuda_launch_api")
```

</details>

#### reports typed CUDA launch evidence through the shared gate classifier

- reports typed CUDA launch evidence through the shared gate classifier
- Verify: reports typed CUDA launch evidence through the shared gate classifier
   - Expected: missing_runtime.success is false
   - Expected: missing_runtime.status_code equals `runtime-not-ready`
   - Expected: missing_runtime.reason equals `cuda-runtime-not-ready`
   - Expected: missing_module.status_code equals `missing-module`
   - Expected: missing_module.reason equals `missing-cuda-generated-module`
   - Expected: missing_args.status_code equals `missing-args-pointer`
   - Expected: missing_args.reason equals `missing-generated-2d-args-pointer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports typed CUDA launch evidence through the shared gate classifier")
step("Verify: reports typed CUDA launch evidence through the shared gate classifier")
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 0)

expect(missing_runtime.success).to_equal(false)
expect(missing_runtime.status_code).to_equal("runtime-not-ready")
expect(missing_runtime.reason).to_equal("cuda-runtime-not-ready")
expect(missing_module.status_code).to_equal("missing-module")
expect(missing_module.reason).to_equal("missing-cuda-generated-module")
expect(missing_args.status_code).to_equal("missing-args-pointer")
expect(missing_args.reason).to_equal("missing-generated-2d-args-pointer")
expect(missing_args.diagnostic_text()).to_contain("CudaSessionEvidence")
```

</details>

#### routes generated bitmap glyph raster through the CUDA session helper

- routes generated bitmap glyph raster through the CUDA session helper
- Verify: routes generated bitmap glyph raster through the CUDA session helper
   - Expected: missing_runtime.operation equals `GENERATED_2D_BITMAP_GLYPH_RASTER`
   - Expected: missing_runtime.entry_name equals `simple_2d_bitmap_glyph_raster_u32`
   - Expected: missing_runtime.typed_status equals `cuda-runtime-unavailable`
   - Expected: missing_module.typed_status equals `cuda-module-unavailable`
   - Expected: missing_args.typed_status equals `args-unavailable`
   - Expected: session.bitmap_glyph_raster_kernel(9, 4, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes generated bitmap glyph raster through the CUDA session helper")
step("Verify: routes generated bitmap glyph raster through the CUDA session helper")
var session = CudaSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 4096)
session.is_initialized = true
session.ctx = 7
val missing_module = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 4096)
session.module_cache = 11
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 0)

expect(missing_runtime.operation).to_equal(GENERATED_2D_BITMAP_GLYPH_RASTER)
expect(missing_runtime.entry_name).to_equal("simple_2d_bitmap_glyph_raster_u32")
expect(missing_runtime.typed_status).to_equal("cuda-runtime-unavailable")
expect(missing_module.typed_status).to_equal("cuda-module-unavailable")
expect(missing_args.typed_status).to_equal("args-unavailable")
expect(missing_args.diagnostic_text()).to_contain("op=bitmap_glyph_raster")
session.module_cache = 0
expect(session.bitmap_glyph_raster_kernel(9, 4, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reports CUDA readback evidence through the shared checksum classifier

- reports CUDA readback evidence through the shared checksum classifier
- Verify: reports CUDA readback evidence through the shared checksum classifier
   - Expected: matched.success is true
   - Expected: matched.status_code equals `readback-matched`
   - Expected: matched.reason equals `readback-checksum-matched`
   - Expected: matched.readback_available is true
   - Expected: unavailable.success is false
   - Expected: unavailable.status_code equals `readback-unavailable`
   - Expected: unavailable.reason equals `device-readback-required`
   - Expected: mismatch.status_code equals `readback-mismatch`
   - Expected: mismatch.reason equals `device-readback-checksum-mismatch`
   - Expected: invalid.status_code equals `invalid-checksum`
   - Expected: invalid.reason equals `device-readback-checksum-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports CUDA readback evidence through the shared checksum classifier")
step("Verify: reports CUDA readback evidence through the shared checksum classifier")
val session = CudaSession.create()
val matched = session.readback_evidence(true, 1234, 1234)
val unavailable = session.readback_evidence(false, 1234, 1234)
val mismatch = session.readback_evidence(true, 1234, 999)
val invalid = session.readback_evidence(true, 0, 1234)

expect(matched.success).to_equal(true)
expect(matched.status_code).to_equal("readback-matched")
expect(matched.reason).to_equal("readback-checksum-matched")
expect(matched.readback_available).to_equal(true)
expect(unavailable.success).to_equal(false)
expect(unavailable.status_code).to_equal("readback-unavailable")
expect(unavailable.reason).to_equal("device-readback-required")
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(mismatch.reason).to_equal("device-readback-checksum-mismatch")
expect(invalid.status_code).to_equal("invalid-checksum")
expect(invalid.reason).to_equal("device-readback-checksum-required")
expect(matched.diagnostic_text()).to_contain("op=readback")
```

</details>

#### shutdown is safe on an uninitialized session

- shutdown is safe on an uninitialized session
- Verify: shutdown is safe on an uninitialized session
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shutdown is safe on an uninitialized session")
step("Verify: shutdown is safe on an uninitialized session")
var session = CudaSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-GPU-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da642be3bd09ffca78072597ef26d60afe274385b4dcdeb74894548967f2e8fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da642be3bd09ffca78072597ef26d60afe274385b4dcdeb74894548967f2e8fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da642be3bd09ffca78072597ef26d60afe274385b4dcdeb74894548967f2e8fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports CUDA kind and availability without initializing hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when launching without a loaded module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails generated 2D launches closed for invalid argument buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
