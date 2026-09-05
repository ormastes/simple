# Graphics 3d Session Managed Backend Specification

> Tests covering Graphics 3D Session Managed Backend, REQ-GFX-001: common backend capability model, REQ-GFX-002: legacy no-session preservation, REQ-GFX-003: managed and perf isolation, REQ-GFX-004: common policy across surfaces, REQ-GFX-005: persistent optimization provider state, REQ-GFX-006: Pure Simple API and C ABI native boundary, REQ-GFX-007: multi-arch capability records.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics 3d Session Managed Backend Specification

## Scenarios

### Graphics 3D Session Managed Backend

### REQ-GFX-001: common backend capability model

#### should report backend kind and target architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GFX-001
# @req REQ-GFX-002
# @req REQ-GFX-003
# @req REQ-GFX-004
# @req REQ-GFX-005
# @req REQ-GFX-006
# @req REQ-GFX-007
```

</details>

#### should reject an unknown backend kind

- should reject an unknown backend kind
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an unknown backend kind")
val result = GraphicsBackendSpec.validate_backend("UnknownGpu")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-002: legacy no-session preservation

#### should map old constructors to LegacyNoSession

- should map old constructors to LegacyNoSession
   - Expected: session.mode equals `LegacyNoSession`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should map old constructors to LegacyNoSession")
val session = GraphicsBackendSpec.create_legacy_3d_session()
expect(session.mode).to_equal("LegacyNoSession")
```

</details>

#### should not enable managed caches for legacy constructors

- should not enable managed caches for legacy constructors
   - Expected: session.managed_cache_enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not enable managed caches for legacy constructors")
val session = GraphicsBackendSpec.create_legacy_2d_session()
expect(session.managed_cache_enabled).to_equal(false)
```

</details>

### REQ-GFX-003: managed and perf isolation

#### should reject mutable resource sharing across modes

- should reject mutable resource sharing across modes
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject mutable resource sharing across modes")
val result = GraphicsBackendSpec.share_mutable_queue("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(true)
```

</details>

#### should allow immutable capability table sharing

- should allow immutable capability table sharing
   - Expected: result.is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow immutable capability table sharing")
val result = GraphicsBackendSpec.share_capability_table("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(false)
```

</details>

### REQ-GFX-004: common policy across surfaces

#### should pass one policy to 2D, 2D game, 3D, web, GUI, and WM

- should pass one policy to 2D, 2D game, 3D, web, GUI, and WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass one policy to 2D, 2D game, 3D, web, GUI, and WM")
val surfaces = GraphicsBackendSpec.bind_policy_to_all_surfaces("ManagedShared")
expect(surfaces).to_contain("engine2d")
expect(surfaces).to_contain("game2d")
expect(surfaces).to_contain("engine3d")
expect(surfaces).to_contain("web_renderer")
expect(surfaces).to_contain("gui")
expect(surfaces).to_contain("wm")
```

</details>

### REQ-GFX-005: persistent optimization provider state

#### should key provider facts by backend and policy hash

- should key provider facts by backend and policy hash
   - Expected: key equals `simple.opt.graphics.pipeline_cache:Metal:abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should key provider facts by backend and policy hash")
val key = GraphicsBackendSpec.provider_key("simple.opt.graphics.pipeline_cache", "Metal", "abc123")
expect(key).to_equal("simple.opt.graphics.pipeline_cache:Metal:abc123")
```

</details>

#### should isolate perf provider state from managed provider state

- should isolate perf provider state from managed provider state
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should isolate perf provider state from managed provider state")
val result = GraphicsBackendSpec.provider_state_aliases("ManagedShared", "PerfExclusive")
expect(result).to_equal(false)
```

</details>

### REQ-GFX-006: Pure Simple API and C ABI native boundary

#### should expose a Pure Simple public API marker

- should expose a Pure Simple public API marker
   - Expected: api.language equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose a Pure Simple public API marker")
val api = GraphicsBackendSpec.public_api_contract()
expect(api.language).to_equal("Simple")
```

</details>

#### should reject Rust as the required runtime backend boundary

- should reject Rust as the required runtime backend boundary
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject Rust as the required runtime backend boundary")
val result = GraphicsBackendSpec.validate_native_boundary("rust-runtime-lib")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-007: multi-arch capability records

#### should include ARM and RISC-V 32/64 targets

- should include ARM and RISC-V 32/64 targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should include ARM and RISC-V 32/64 targets")
val targets = GraphicsBackendSpec.supported_arch_records()
expect(targets).to_contain("arm32")
expect(targets).to_contain("arm64")
expect(targets).to_contain("riscv32")
expect(targets).to_contain("riscv64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Graphics 3D Session Managed Backend, REQ-GFX-001: common backend capability model, REQ-GFX-002: legacy no-session preservation, REQ-GFX-003: managed and perf isolation, REQ-GFX-004: common policy across surfaces, REQ-GFX-005: persistent optimization provider state, REQ-GFX-006: Pure Simple API and C ABI native boundary, REQ-GFX-007: multi-arch capability records.
- Graphics 3D Session Managed Backend
- REQ-GFX-001: common backend capability model
- REQ-GFX-002: legacy no-session preservation
- REQ-GFX-003: managed and perf isolation
- REQ-GFX-004: common policy across surfaces
- REQ-GFX-005: persistent optimization provider state
- REQ-GFX-006: Pure Simple API and C ABI native boundary
- REQ-GFX-007: multi-arch capability records

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GFX-001`
- `REQ-GFX-002`
- `REQ-GFX-003`
- `REQ-GFX-004`
- `REQ-GFX-005`
- `REQ-GFX-006`
- `REQ-GFX-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64fc1239eb7ba5a1e11ef85c7bb28878b3ca3c982982282c0e5e731668b0883d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64fc1239eb7ba5a1e11ef85c7bb28878b3ca3c982982282c0e5e731668b0883d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64fc1239eb7ba5a1e11ef85c7bb28878b3ca3c982982282c0e5e731668b0883d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl
mirror: doc/06_spec/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md (current)
findings: 13 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should report backend kind and target architecture' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report backend kind and target architecture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unknown backend kind' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an unknown backend kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map old constructors to LegacyNoSession' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should map old constructors to LegacyNoSession' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not enable managed caches for legacy constructors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should not enable managed caches for legacy constructors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject mutable resource sharing across modes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow immutable capability table sharing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
