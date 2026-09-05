# Simple Wm Performance Specification

> <details>

<!-- sdn-diagram:id=simple_wm_performance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_wm_performance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_wm_performance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_wm_performance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Wm Performance Specification

## Scenarios

### Simple WM production performance

#### should measure ten warm production host launches after one discarded launch

- Record the reference host OS CPU GPU RAM display and power state
   - Artifact capture: after_step
- Launch the cached production pure-Simple host WM once and discard the cold sample
   - Artifact capture: after_step
- Measure ten warm launches to the first presented shared-scene frame
   - Artifact capture: after_step
- Validate all raw startup samples budgets freshness and provenance
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the reference host OS CPU GPU RAM display and power state")
step("Launch the cached production pure-Simple host WM once and discard the cold sample")
step("Measure ten warm launches to the first presented shared-scene frame")
val report = measure_host_warm_startup_10()
step("Validate all raw startup samples budgets freshness and provenance")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>

<details>
<summary>Advanced: should bound thirty acknowledged host fullscreen mode pairs</summary>

#### should bound thirty acknowledged host fullscreen mode pairs

- Launch the cached production pure-Simple host WM in windowed mode
   - Log capture: after_step
- Measure thirty fullscreen enter and exit pairs against matching physical acknowledgements
   - Log capture: after_step
- Compute nearest-rank p95 and validate raw nonce-correlated samples
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the cached production pure-Simple host WM in windowed mode")
step("Measure thirty fullscreen enter and exit pairs against matching physical acknowledgements")
val report = measure_host_mode_transition_pairs_30()
step("Compute nearest-rank p95 and validate raw nonce-correlated samples")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should bound six hundred accelerated frame durations after sixty discarded frames</summary>

#### should bound six hundred accelerated frame durations after sixty discarded frames

- Launch the production host WM with an explicitly required accelerated backend
   - Log capture: after_step
- Render six hundred sixty revision-correlated frames at 1920x1080
   - Log capture: after_step
- Discard sixty warmup frames and measure the remaining six hundred frames
   - Log capture: after_step
- Require nearest-rank p95 at or below 16.7 milliseconds with no fallback
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production host WM with an explicitly required accelerated backend")
step("Render six hundred sixty revision-correlated frames at 1920x1080")
step("Discard sixty warmup frames and measure the remaining six hundred frames")
val report = measure_host_frame_pacing_600("accelerated")
step("Require nearest-rank p95 at or below 16.7 milliseconds with no fallback")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should bound an explicitly requested typed fallback frame row</summary>

#### should bound an explicitly requested typed fallback frame row

- Request the typed fallback row explicitly and retain the accelerated failure
   - Log capture: after_step
- Render six hundred sixty revision-correlated frames at 1920x1080
   - Log capture: after_step
- Discard sixty warmup frames and measure the remaining six hundred frames
   - Log capture: after_step
- Require nearest-rank p95 at or below 50 milliseconds and validate fallback provenance
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request the typed fallback row explicitly and retain the accelerated failure")
step("Render six hundred sixty revision-correlated frames at 1920x1080")
step("Discard sixty warmup frames and measure the remaining six hundred frames")
val report = measure_host_frame_pacing_600("typed-fallback")
step("Require nearest-rank p95 at or below 50 milliseconds and validate fallback provenance")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should bound final RSS and final-fifty slope after one hundred host mode pairs</summary>

#### should bound final RSS and final-fifty slope after one hundred host mode pairs

- Launch the production host WM and record stable baseline process RSS
   - Log capture: after_step
- Measure process RSS after each of one hundred completed mode pairs
   - Log capture: after_step
- Validate final growth bound and nonpositive least-squares slope over the final fifty samples
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the production host WM and record stable baseline process RSS")
step("Measure process RSS after each of one hundred completed mode pairs")
val report = measure_host_rss_pairs_100()
step("Validate final growth bound and nonpositive least-squares slope over the final fifty samples")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should bound thirty SimpleOS emulated-device input to framebuffer pairs</summary>

#### should bound thirty SimpleOS emulated-device input to framebuffer pairs

- Boot the production pure-Simple SimpleOS image with the documented fixed idle QEMU configuration
   - Artifact capture: after_step
- Inject thirty inputs through the emulated hardware input device
   - Artifact capture: after_step
- Correlate IRQ driver WM revisions and matching framebuffer generations
   - Artifact capture: after_step
- Compute nearest-rank p95 and validate QEMU configuration samples and provenance
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the production pure-Simple SimpleOS image with the documented fixed idle QEMU configuration")
step("Inject thirty inputs through the emulated hardware input device")
step("Correlate IRQ driver WM revisions and matching framebuffer generations")
val report = measure_simpleos_qemu_input_pairs_30()
step("Compute nearest-rank p95 and validate QEMU configuration samples and provenance")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should validate every physical scale and viewport matrix row</summary>

#### should validate every physical scale and viewport matrix row

- Launch production host and SimpleOS shared-scene renderers
   - Artifact capture: after_step
- Drive physical resize and scale events across the sixteen matrix rows
   - Artifact capture: after_step
- Validate layout invariants captured pixels and row provenance
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: verify_every_performance_row_provenance(report) equals `verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch production host and SimpleOS shared-scene renderers")
step("Drive physical resize and scale events across the sixteen matrix rows")
val report = measure_dpi_viewport_matrix()
step("Validate layout invariants captured pixels and row provenance")
expect(verify_every_performance_row_provenance(report)).to_equal("verified")
```

</details>


</details>

<details>
<summary>Advanced: should reject every performance budget breach</summary>

#### should reject every performance budget breach

- Submit startup mode accelerated fallback QEMU RSS-growth and RSS-slope budget breaches
   - Log capture: after_step
   - Evidence: log output verified by 7 expected checks
   - Expected: submit_invalid_performance_evidence("startup-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("mode-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("accelerated-frame-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("typed-fallback-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("qemu-input-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("rss-growth-budget-breach") equals `rejected`
   - Expected: submit_invalid_performance_evidence("rss-positive-slope") equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit startup mode accelerated fallback QEMU RSS-growth and RSS-slope budget breaches")
expect(submit_invalid_performance_evidence("startup-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("mode-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("accelerated-frame-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("typed-fallback-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("qemu-input-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("rss-growth-budget-breach")).to_equal("rejected")
expect(submit_invalid_performance_evidence("rss-positive-slope")).to_equal("rejected")
```

</details>


</details>

<details>
<summary>Advanced: should reject silent unrequested or misclassified fallback rows</summary>

#### should reject silent unrequested or misclassified fallback rows

- Submit accelerated rows that silently use fallback or omit typed fallback evidence
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: submit_invalid_performance_evidence("silent-fallback") equals `rejected`
   - Expected: submit_invalid_performance_evidence("unrequested-fallback") equals `rejected`
   - Expected: submit_invalid_performance_evidence("fallback-without-accelerated-failure") equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit accelerated rows that silently use fallback or omit typed fallback evidence")
expect(submit_invalid_performance_evidence("silent-fallback")).to_equal("rejected")
expect(submit_invalid_performance_evidence("unrequested-fallback")).to_equal("rejected")
expect(submit_invalid_performance_evidence("fallback-without-accelerated-failure")).to_equal("rejected")
```

</details>


</details>

<details>
<summary>Advanced: should reject stale incomplete fabricated or nonproduction rows</summary>

#### should reject stale incomplete fabricated or nonproduction rows

- Submit stale missing corrupt partial synthetic seed and source-only evidence rows
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: submit_invalid_performance_evidence("stale-report") equals `rejected`
   - Expected: submit_invalid_performance_evidence("missing-provenance") equals `rejected`
   - Expected: submit_invalid_performance_evidence("fabricated-samples") equals `rejected`
   - Expected: submit_invalid_performance_evidence("seed-provenance") equals `rejected`
   - Expected: submit_invalid_performance_evidence("source-only-pass") equals `rejected`
   - Expected: submit_invalid_performance_evidence("fixed-scanout-metadata") equals `rejected`
   - Expected: submit_invalid_performance_evidence("missing-dependency") equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit stale missing corrupt partial synthetic seed and source-only evidence rows")
expect(submit_invalid_performance_evidence("stale-report")).to_equal("rejected")
expect(submit_invalid_performance_evidence("missing-provenance")).to_equal("rejected")
expect(submit_invalid_performance_evidence("fabricated-samples")).to_equal("rejected")
expect(submit_invalid_performance_evidence("seed-provenance")).to_equal("rejected")
expect(submit_invalid_performance_evidence("source-only-pass")).to_equal("rejected")
expect(submit_invalid_performance_evidence("fixed-scanout-metadata")).to_equal("rejected")
expect(submit_invalid_performance_evidence("missing-dependency")).to_equal("rejected")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_performance_spec.spl` |
| Updated | 2026-07-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple WM production performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
