# graphics_3d_session_managed_backend_spec

> Verifies the graphics 3d session managed backend behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# graphics_3d_session_managed_backend_spec

Verifies the graphics 3d session managed backend behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the graphics 3d session managed backend behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Graphics 3D Session Managed Backend

### REQ-GFX-001: common backend capability model

#### should report backend kind and target architecture

- Verify: should report backend kind and target architecture
   - Expected: caps.backend_kind equals `Vulkan`
   - Expected: caps.target_arch equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should report backend kind and target architecture")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val caps = GraphicsBackendSpec.fake_caps("Vulkan", "riscv64")
expect(caps.backend_kind).to_equal("Vulkan")
expect(caps.target_arch).to_equal("riscv64")
```

</details>

#### should reject an unknown backend kind

- Verify: should reject an unknown backend kind
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should reject an unknown backend kind")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = GraphicsBackendSpec.validate_backend("UnknownGpu")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-002: legacy no-session preservation

#### should map old constructors to LegacyNoSession

- Verify: should map old constructors to LegacyNoSession
   - Expected: session.mode equals `LegacyNoSession`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should map old constructors to LegacyNoSession")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val session = GraphicsBackendSpec.create_legacy_3d_session()
expect(session.mode).to_equal("LegacyNoSession")
```

</details>

#### should not enable managed caches for legacy constructors

- Verify: should not enable managed caches for legacy constructors
   - Expected: session.managed_cache_enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should not enable managed caches for legacy constructors")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val session = GraphicsBackendSpec.create_legacy_2d_session()
expect(session.managed_cache_enabled).to_equal(false)
```

</details>

### REQ-GFX-003: managed and perf isolation

#### should reject mutable resource sharing across modes

- Verify: should reject mutable resource sharing across modes
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should reject mutable resource sharing across modes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = GraphicsBackendSpec.share_mutable_queue("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(true)
```

</details>

#### should allow immutable capability table sharing

- Verify: should allow immutable capability table sharing
   - Expected: result.is_err() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should allow immutable capability table sharing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = GraphicsBackendSpec.share_capability_table("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(false)
```

</details>

### REQ-GFX-004: common policy across surfaces

#### should pass one policy to 2D, 2D game, 3D, web, GUI, and WM

- Verify: should pass one policy to 2D, 2D game, 3D, web, GUI, and WM


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should pass one policy to 2D, 2D game, 3D, web, GUI, and WM")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should key provider facts by backend and policy hash
   - Expected: key equals `simple.opt.graphics.pipeline_cache:Metal:abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should key provider facts by backend and policy hash")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val key = GraphicsBackendSpec.provider_key("simple.opt.graphics.pipeline_cache", "Metal", "abc123")
expect(key).to_equal("simple.opt.graphics.pipeline_cache:Metal:abc123")
```

</details>

#### should isolate perf provider state from managed provider state

- Verify: should isolate perf provider state from managed provider state
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should isolate perf provider state from managed provider state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = GraphicsBackendSpec.provider_state_aliases("ManagedShared", "PerfExclusive")
expect(result).to_equal(false)
```

</details>

### REQ-GFX-006: Pure Simple API and C ABI native boundary

#### should expose a Pure Simple public API marker

- Verify: should expose a Pure Simple public API marker
   - Expected: api.language equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should expose a Pure Simple public API marker")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val api = GraphicsBackendSpec.public_api_contract()
expect(api.language).to_equal("Simple")
```

</details>

#### should reject Rust as the required runtime backend boundary

- Verify: should reject Rust as the required runtime backend boundary
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should reject Rust as the required runtime backend boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val result = GraphicsBackendSpec.validate_native_boundary("rust-runtime-lib")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-007: multi-arch capability records

#### should include ARM and RISC-V 32/64 targets

- Verify: should include ARM and RISC-V 32/64 targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-GFX-001 REQ-GFX-002 REQ-GFX-003 REQ-GFX-004 REQ-GFX-005 REQ-GFX-006 REQ-GFX-007
step("Verify: should include ARM and RISC-V 32/64 targets")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val targets = GraphicsBackendSpec.supported_arch_records()
expect(targets).to_contain("arm32")
expect(targets).to_contain("arm64")
expect(targets).to_contain("riscv32")
expect(targets).to_contain("riscv64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1ba89a07d41ff930439b1912f50d0bacefddc6efc7bb7c14f47a88f29de2a5c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1ba89a07d41ff930439b1912f50d0bacefddc6efc7bb7c14f47a88f29de2a5c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1ba89a07d41ff930439b1912f50d0bacefddc6efc7bb7c14f47a88f29de2a5c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl
mirror: doc/06_spec/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report backend kind and target architecture' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unknown backend kind' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map old constructors to LegacyNoSession' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not enable managed caches for legacy constructors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject mutable resource sharing across modes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow immutable capability table sharing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
