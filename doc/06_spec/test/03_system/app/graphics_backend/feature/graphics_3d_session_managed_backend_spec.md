# Graphics 3d Session Managed Backend Specification

> <details>

<!-- sdn-diagram:id=graphics_3d_session_managed_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graphics_3d_session_managed_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graphics_3d_session_managed_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graphics_3d_session_managed_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = GraphicsBackendSpec.fake_caps("Vulkan", "riscv64")
expect(caps.backend_kind).to_equal("Vulkan")
expect(caps.target_arch).to_equal("riscv64")
```

</details>

#### should reject an unknown backend kind

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = GraphicsBackendSpec.validate_backend("UnknownGpu")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-002: legacy no-session preservation

#### should map old constructors to LegacyNoSession

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = GraphicsBackendSpec.create_legacy_3d_session()
expect(session.mode).to_equal("LegacyNoSession")
```

</details>

#### should not enable managed caches for legacy constructors

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = GraphicsBackendSpec.create_legacy_2d_session()
expect(session.managed_cache_enabled).to_equal(false)
```

</details>

### REQ-GFX-003: managed and perf isolation

#### should reject mutable resource sharing across modes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = GraphicsBackendSpec.share_mutable_queue("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(true)
```

</details>

#### should allow immutable capability table sharing

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = GraphicsBackendSpec.share_capability_table("ManagedShared", "PerfExclusive")
expect(result.is_err()).to_equal(false)
```

</details>

### REQ-GFX-004: common policy across surfaces

#### should pass one policy to 2D, 2D game, 3D, web, GUI, and WM

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = GraphicsBackendSpec.provider_key("simple.opt.graphics.pipeline_cache", "Metal", "abc123")
expect(key).to_equal("simple.opt.graphics.pipeline_cache:Metal:abc123")
```

</details>

#### should isolate perf provider state from managed provider state

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = GraphicsBackendSpec.provider_state_aliases("ManagedShared", "PerfExclusive")
expect(result).to_equal(false)
```

</details>

### REQ-GFX-006: Pure Simple API and C ABI native boundary

#### should expose a Pure Simple public API marker

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val api = GraphicsBackendSpec.public_api_contract()
expect(api.language).to_equal("Simple")
```

</details>

#### should reject Rust as the required runtime backend boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = GraphicsBackendSpec.validate_native_boundary("rust-runtime-lib")
expect(result.is_err()).to_equal(true)
```

</details>

### REQ-GFX-007: multi-arch capability records

#### should include ARM and RISC-V 32/64 targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
