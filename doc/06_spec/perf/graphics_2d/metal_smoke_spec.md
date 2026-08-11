# metal_smoke_spec

test/05_perf/graphics_2d/metal_smoke_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-4 — Metal backend macOS-gated correctness verification |
| Category | Graphics \| Backend \| Metal |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/metal_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/05_perf/graphics_2d/metal_smoke_spec.spl

Verifies that the Metal backend:
  - Wires MTLComputePipelineState and dispatch
  - Correctness verified via sync_readback pixel hash match
  - Test is gated: only runs when macOS and Metal are available
  - probe() reports shader_format == "msl"

Note: on non-macOS hosts, the probe result status is Failed and
the it blocks that check pixel hash are skipped at runtime by the
implementation — the spec still declares the expected behavior.

@cover src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl
@cover src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl

## Scenarios

### backend_metal — AC-4: Metal macOS-gated

### Metal probe identity

#### AC-4: Metal probe reports backend name metal

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.backend).to_equal(METAL_BACKEND_NAME)
```

</details>

#### AC-4: Metal probe reports shader_format msl

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.shader_format).to_equal(METAL_SHADER_FORMAT)
```

</details>

#### AC-4: Metal probe reports api_name metal

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.api_name).to_equal(METAL_API_NAME)
```

</details>

#### AC-4: Metal status is Ok when available

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.status).to_equal("Ok")
```

</details>

#### AC-4: Metal status is Failed when not on macOS

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.status).to_equal("Failed")
```

</details>

### MTLComputePipelineState

#### AC-4: pipeline_state_ok is true when Metal is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.pipeline_state_ok).to_equal(true)
```

</details>

#### AC-4: dispatch_ok is true when pipeline state is ready

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.dispatch_ok).to_equal(true)
```

</details>

#### AC-4: pipeline_state_ok is false when Metal is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.pipeline_state_ok).to_equal(false)
```

</details>

### correctness via sync_readback

#### AC-4: sync_readback completes when Metal is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.readback_completed).to_equal(true)
```

</details>

#### AC-4: Metal pixel hash matches CPU reference hash

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(metal_hashes_match(s)).to_equal(true)
```

</details>

#### AC-4: metal_pixel_hash equals cpu_pixel_hash exactly

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_smoke_ok()
expect(s.metal_pixel_hash).to_equal(s.cpu_pixel_hash)
```

</details>

#### AC-4: readback is not completed when Metal is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: MetalSmokeSentinel = make_metal_unavailable()
expect(s.readback_completed).to_equal(false)
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

