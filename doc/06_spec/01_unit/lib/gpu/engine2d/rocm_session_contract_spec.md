# rocm_session_contract_spec

> Purpose: Prove that RocmSession compute contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rocm_session_contract_spec

Purpose: Prove that RocmSession compute contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RocmSession compute contract.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### RocmSession compute contract

#### reports ROCm kind and unavailable without an injected HIP FFI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports ROCm kind and unavailable without an injected HIP FFI
- Verify: reports ROCm kind and unavailable without an injected HIP FFI
   - Expected: session.kind() equals `BackendSessionKind.Rocm`
   - Expected: session.is_available() is false
   - Expected: session.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports ROCm kind and unavailable without an injected HIP FFI")
step("Verify: reports ROCm kind and unavailable without an injected HIP FFI")
# @req: REQ-LIB-GPU-001
val session = RocmSession.create()

expect(session.kind()).to_equal(BackendSessionKind.Rocm)
expect(session.is_available()).to_equal(false)
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when initializing or launching without HIP FFI

- fails closed when initializing or launching without HIP FFI
- Verify: fails closed when initializing or launching without HIP FFI
   - Expected: session.init() equals `1`
   - Expected: session.load_module("") equals `0`
   - Expected: session.alloc(16) equals `0`
   - Expected: session.read_pixels(1, [], 16) is false
   - Expected: session.synchronize() equals `1`
   - Expected: session.launch_kernel("kernel_clear", 1, 1, 1, 1) equals `1`
   - Expected: session.fill_kernel(64, 64, 4096) equals `1`
   - Expected: session.copy_kernel(64, 64, 4096) equals `1`
   - Expected: session.alpha_blend_kernel(64, 64, 4096) equals `1`
   - Expected: session.scroll_kernel(64, 64, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when initializing or launching without HIP FFI")
step("Verify: fails closed when initializing or launching without HIP FFI")
val session = RocmSession.create()

expect(session.init()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.load_module("")).to_equal(0)
expect(session.alloc(16)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(session.read_pixels(1, [], 16)).to_equal(false)
expect(session.synchronize()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.launch_kernel("kernel_clear", 1, 1, 1, 1)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
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
var session = RocmSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### reports shared generated 2D runtime provenance without HIP FFI

- reports shared generated 2D runtime provenance without HIP FFI
- Verify: reports shared generated 2D runtime provenance without HIP FFI
   - Expected: missing_runtime.ready is false
   - Expected: missing_runtime.typed_status equals `hip-runtime-unavailable`
   - Expected: still_missing_runtime.ready is false
   - Expected: still_missing_runtime.typed_status equals `hip-runtime-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports shared generated 2D runtime provenance without HIP FFI")
step("Verify: reports shared generated 2D runtime provenance without HIP FFI")
var session = RocmSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_ALPHA, 64, 64, 4096)
session.is_initialized = true
session.module_cache = 11
val still_missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_ALPHA, 64, 64, 4096)

expect(missing_runtime.ready).to_equal(false)
expect(missing_runtime.typed_status).to_equal("hip-runtime-unavailable")
expect(still_missing_runtime.ready).to_equal(false)
expect(still_missing_runtime.typed_status).to_equal("hip-runtime-unavailable")
expect(still_missing_runtime.diagnostic_text()).to_contain("launch=rt_rocm_launch_kernel")
```

</details>

#### reports typed ROCm session evidence for generated module launch and readback gates

- reports typed ROCm session evidence for generated module launch and readback gates
- Verify: reports typed ROCm session evidence for generated module launch and readback gates
   - Expected: init_ev.success is false
   - Expected: init_ev.status_code equals `missing-ffi`
   - Expected: load_ev.success is false
   - Expected: load_ev.reason equals `missing-rocm-ffi`
   - Expected: launch_missing_args.status_code equals `missing-args-pointer`
   - Expected: launch_missing_ffi.status_code equals `missing-ffi`
   - Expected: read_ev.status_code equals `missing-ffi`
   - Expected: matched.success is true
   - Expected: matched.status_code equals `readback-matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports typed ROCm session evidence for generated module launch and readback gates")
step("Verify: reports typed ROCm session evidence for generated module launch and readback gates")
var session = RocmSession.create()
val init_ev = session.init_evidence()
val load_ev = session.load_module_evidence(rocm_2d_generated_source())
val launch_missing_args = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 0)
val launch_missing_ffi = session.launch_generated_2d_evidence(GENERATED_2D_FILL, 8, 8, 4096)
val read_ev = session.read_pixels_evidence(0, [], 0, 1, 1)
val matched = session.readback_evidence(true, 99, 99)

expect(init_ev.success).to_equal(false)
expect(init_ev.status_code).to_equal("missing-ffi")
expect(load_ev.success).to_equal(false)
expect(load_ev.reason).to_equal("missing-rocm-ffi")
expect(launch_missing_args.status_code).to_equal("missing-args-pointer")
expect(launch_missing_ffi.status_code).to_equal("missing-ffi")
expect(read_ev.status_code).to_equal("missing-ffi")
expect(matched.success).to_equal(true)
expect(matched.status_code).to_equal("readback-matched")
```

</details>

#### static HIP FFI exposes runtime-backed init evidence without missing FFI

- static HIP FFI exposes runtime-backed init evidence without missing FFI
- Verify: static HIP FFI exposes runtime-backed init evidence without missing FFI
   - Expected: init_ev.status_code == "initialized" or init_ev.status_code == "runtime-unavailable" or init_ev.status_code == "device-unavailable" or init_ev.status_code == "init-failed" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("static HIP FFI exposes runtime-backed init evidence without missing FFI")
step("Verify: static HIP FFI exposes runtime-backed init evidence without missing FFI")
var session = RocmSession.create_with_ffi(RocmFfi.create_static())
val init_ev = session.init_evidence()

expect(init_ev.reason).to_not_equal("missing-rocm-ffi")
expect(init_ev.status_code == "initialized" or init_ev.status_code == "runtime-unavailable" or init_ev.status_code == "device-unavailable" or init_ev.status_code == "init-failed").to_equal(true)
session.shutdown()
```

</details>

#### exports the HIP nonzero image blit kernel for transparent text

- exports the HIP nonzero image blit kernel for transparent text
- Verify: exports the HIP nonzero image blit kernel for transparent text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports the HIP nonzero image blit kernel for transparent text")
step("Verify: exports the HIP nonzero image blit kernel for transparent text")
val source = _engine2d_hip_source()

expect(source).to_contain("kernel_blit_image_nonzero")
expect(source).to_contain("if (pixel == 0) return")
```

</details>

#### exports shared generated HIP kernels with CUDA and OpenCL entry names

- exports shared generated HIP kernels with CUDA and OpenCL entry names
- Verify: exports shared generated HIP kernels with CUDA and OpenCL entry names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports shared generated HIP kernels with CUDA and OpenCL entry names")
step("Verify: exports shared generated HIP kernels with CUDA and OpenCL entry names")
val source = rocm_2d_generated_source()

expect(source).to_contain("simple_2d_fill_u32")
expect(source).to_contain("simple_2d_copy_u32")
expect(source).to_contain("simple_2d_alpha_u32")
expect(source).to_contain("simple_2d_scroll_u32")
expect(source).to_contain("simple_2d_bitmap_glyph_raster_u32")
```

</details>

#### routes generated bitmap glyph raster through the ROCm session helper

- routes generated bitmap glyph raster through the ROCm session helper
- Verify: routes generated bitmap glyph raster through the ROCm session helper
   - Expected: missing_runtime.operation equals `GENERATED_2D_BITMAP_GLYPH_RASTER`
   - Expected: missing_runtime.entry_name equals `simple_2d_bitmap_glyph_raster_u32`
   - Expected: missing_runtime.typed_status equals `hip-runtime-unavailable`
   - Expected: missing_args.typed_status equals `hip-runtime-unavailable`
   - Expected: session.bitmap_glyph_raster_kernel(9, 4, 4096) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes generated bitmap glyph raster through the ROCm session helper")
step("Verify: routes generated bitmap glyph raster through the ROCm session helper")
var session = RocmSession.create()
val missing_runtime = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 4096)
session.is_initialized = true
session.module_cache = 11
val missing_args = session.launch_generated_2d_runtime_provenance(GENERATED_2D_BITMAP_GLYPH_RASTER, 8, 4, 0)

expect(missing_runtime.operation).to_equal(GENERATED_2D_BITMAP_GLYPH_RASTER)
expect(missing_runtime.entry_name).to_equal("simple_2d_bitmap_glyph_raster_u32")
expect(missing_runtime.typed_status).to_equal("hip-runtime-unavailable")
expect(missing_args.typed_status).to_equal("hip-runtime-unavailable")
expect(missing_args.diagnostic_text()).to_contain("op=bitmap_glyph_raster")
session.module_cache = 0
expect(session.bitmap_glyph_raster_kernel(9, 4, 4096)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `6d74b542092a0c484b2d39819fbdb4b3f4b255f2d47bfcdcacf57cbc2623c983`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d74b542092a0c484b2d39819fbdb4b3f4b255f2d47bfcdcacf57cbc2623c983`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d74b542092a0c484b2d39819fbdb4b3f4b255f2d47bfcdcacf57cbc2623c983`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports ROCm kind and unavailable without an injected HIP FFI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when initializing or launching without HIP FFI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shutdown is safe on an uninitialized session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
