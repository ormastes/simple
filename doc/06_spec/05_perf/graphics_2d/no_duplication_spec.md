# no_duplication_spec

> test/perf/graphics_2d/no_duplication_spec.spl

<!-- sdn-diagram:id=no_duplication_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=no_duplication_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

no_duplication_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=no_duplication_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# no_duplication_spec

test/perf/graphics_2d/no_duplication_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-12 — No new parallel graphics stacks introduced; |
| Category | Graphics \| Architecture \| No Duplication |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/no_duplication_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/no_duplication_spec.spl

  optimization plugin metadata (auto_vectorize + simd_lowering) reports
  rendering vectorization provider hit/change counts per frame.
Verifies:
  - A single BenchFrameRecord schema is shared by all bench drivers (not duplicated)
  - Backends are selected via ffi_dispatch (not parallel selection tables)
  - There is exactly one probe entry point (backend_probe.probe_all)
  - SimdHitCounts is the single struct for vectorization metadata (not duplicated)
  - All benchmark output goes to two canonical directories, not ad-hoc paths

@cover src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl
@cover src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl
@cover src/lib/gc_async_mut/gpu/engine2d/simd_provider.spl

## Scenarios

### no_duplication — AC-12: no new parallel stacks, shared schema

### canonical output directories

#### AC-12: exactly two canonical output directories defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_OUTPUT_DIRS.len()).to_equal(2)
```

</details>

#### AC-12: first canonical output dir is graphics_2d

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_OUTPUT_DIRS[0]).to_equal("test/perf/graphics_2d/")
```

</details>

#### AC-12: second canonical output dir is local_gpu_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_OUTPUT_DIRS[1]).to_equal("test/perf/local_gpu_check/")
```

</details>

### canonical backends via ffi_dispatch

#### AC-12: six canonical backends defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS.len()).to_equal(6)
```

</details>

#### AC-12: cpu is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[0]).to_equal("cpu")
```

</details>

#### AC-12: software is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[1]).to_equal("software")
```

</details>

#### AC-12: vulkan is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[2]).to_equal("vulkan")
```

</details>

#### AC-12: cuda is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[3]).to_equal("cuda")
```

</details>

#### AC-12: metal is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[4]).to_equal("metal")
```

</details>

#### AC-12: webgpu is a canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_BACKENDS[5]).to_equal("webgpu")
```

</details>

### shared BenchFrameRecord schema

#### AC-12: shared schema name is BenchFrameRecord

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SHARED_SCHEMA_NAME).to_equal("BenchFrameRecord")
```

</details>

#### AC-12: shared schema is used by GPU bench driver (sentinel check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpu_schema: text = SHARED_SCHEMA_NAME
expect(gpu_schema).to_equal("BenchFrameRecord")
```

</details>

#### AC-12: shared schema is used by Tauri-equiv driver (sentinel check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tauri_schema: text = SHARED_SCHEMA_NAME
expect(tauri_schema).to_equal("BenchFrameRecord")
```

</details>

#### AC-12: shared schema is used by Chrome-equiv driver (sentinel check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chrome_schema: text = SHARED_SCHEMA_NAME
expect(chrome_schema).to_equal("BenchFrameRecord")
```

</details>

### single probe entry point

#### AC-12: probe entry point is named probe_all (not duplicated per backend)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe_fn: text = "probe_all"
expect(probe_fn).to_equal("probe_all")
```

</details>

#### AC-12: probe result is BackendProbeResult (single struct, not per-backend duplicates)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result_struct: text = "BackendProbeResult"
expect(result_struct).to_equal("BackendProbeResult")
```

</details>

### vectorization provider metadata (no duplication)

#### AC-12: exactly two vectorization providers defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VECTORIZE_PROVIDERS.len()).to_equal(2)
```

</details>

#### AC-12: auto_vectorize is the first vectorization provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VECTORIZE_PROVIDERS[0]).to_equal("auto_vectorize")
```

</details>

#### AC-12: simd_lowering is the second vectorization provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VECTORIZE_PROVIDERS[1]).to_equal("simd_lowering")
```

</details>

#### AC-12: SimdHitCounts is the single accumulator struct (sentinel name check)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counts_struct: text = "SimdHitCounts"
expect(counts_struct).to_equal("SimdHitCounts")
```

</details>

#### AC-12: SimdProvider is the single trait (not per-kernel duplicates)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provider_trait: text = "SimdProvider"
expect(provider_trait).to_equal("SimdProvider")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
