# optimization_plugin_spec

> test/perf/graphics_2d/optimization_plugin_spec.spl

<!-- sdn-diagram:id=optimization_plugin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=optimization_plugin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

optimization_plugin_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=optimization_plugin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# optimization_plugin_spec

test/perf/graphics_2d/optimization_plugin_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-10 (state.md) — optimization plugin metadata: |
| Category | Graphics \| Compiler \| Optimization Plugin |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/optimization_plugin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/optimization_plugin_spec.spl

  auto_vectorize + simd_lowering report rendering vectorization provider
  hit/change counts per frame.
Verifies:
  - plugin_hook_vectorize_event is called with (kernel_id, changed) per frame
  - SimdHitCounts accumulates hit and change events
  - provider metadata is accessible from the benchmark report
  - active_providers list is reported in BenchFrameRecord

@cover src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl
@cover src/lib/gc_async_mut/gpu/engine2d/simd_provider.spl

## Scenarios

### optimization_plugin — AC-10: provider hit/change metadata

### provider name constants

#### AC-10: auto_vectorize provider name is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PROVIDER_AUTO_VECTORIZE).to_equal("auto_vectorize")
```

</details>

#### AC-10: simd_lowering provider name is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PROVIDER_SIMD_LOWERING).to_equal("simd_lowering")
```

</details>

#### AC-10: two optimization providers are defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val providers: [text] = [PROVIDER_AUTO_VECTORIZE, PROVIDER_SIMD_LOWERING]
expect(providers.len()).to_equal(2)
```

</details>

### provider event structure

#### AC-10: event carries kernel_id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.kernel_id).to_equal("fill")
```

</details>

#### AC-10: event carries changed field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.changed).to_equal(true)
```

</details>

#### AC-10: event carries provider field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.provider).to_equal(PROVIDER_AUTO_VECTORIZE)
```

</details>

#### AC-10: unchanged event has changed == false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e: ProviderEventSentinel = make_provider_event("alpha_blend", false, PROVIDER_AUTO_VECTORIZE)
expect(e.changed).to_equal(false)
```

</details>

### ProviderReport accumulation

#### AC-10: report frame_id is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.frame_id > 0).to_equal(true)
```

</details>

#### AC-10: active_providers contains auto_vectorize

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.active_providers[0]).to_equal(PROVIDER_AUTO_VECTORIZE)
```

</details>

#### AC-10: active_providers contains simd_lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.active_providers[1]).to_equal(PROVIDER_SIMD_LOWERING)
```

</details>

#### AC-10: five events are recorded in one frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.events.len()).to_equal(5)
```

</details>

#### AC-10: total_hits is greater than zero after a frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.total_hits > 0).to_equal(true)
```

</details>

#### AC-10: total_changes matches events with changed == true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
val counted: i64 = count_changes(r)
expect(counted).to_equal(r.total_changes)
```

</details>

#### AC-10: total_changes is less than or equal to total_hits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.total_changes <= r.total_hits).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
