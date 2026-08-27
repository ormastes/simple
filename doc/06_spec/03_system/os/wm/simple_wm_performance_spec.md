# Simple WM Production Performance

> Measures the cached production pure-Simple host WM and SimpleOS WM with raw,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple WM Production Performance

Measures the cached production pure-Simple host WM and SimpleOS WM with raw,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/simple_wm_performance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Measures the cached production pure-Simple host WM and SimpleOS WM with raw,
fresh runtime evidence. The operator flow defines warm startup, acknowledged
mode transition, frame pacing, RSS stability, emulated-device input latency,
render provenance, and the physical DPI/viewport matrix.

Every runtime helper fails explicitly until the production harness implements
it. Source inspection, synthetic samples, seed execution, canned captures,
fixed scanout metadata, and reused reports cannot satisfy this specification.

## Scenarios

### Simple WM production performance

#### should measure ten warm production host launches after one discarded launch

- should measure ten warm production host launches after one discarded launch
   - Artifact capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should measure ten warm production host launches after one discarded launch")
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

- should bound thirty acknowledged host fullscreen mode pairs
   - Log capture: after_step
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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound thirty acknowledged host fullscreen mode pairs")
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

- should bound six hundred accelerated frame durations after sixty discarded frames
   - Log capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound six hundred accelerated frame durations after sixty discarded frames")
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

- should bound an explicitly requested typed fallback frame row
   - Log capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound an explicitly requested typed fallback frame row")
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

- should bound final RSS and final-fifty slope after one hundred host mode pairs
   - Log capture: after_step
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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound final RSS and final-fifty slope after one hundred host mode pairs")
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

- should bound thirty SimpleOS emulated-device input to framebuffer pairs
   - Artifact capture: after_step
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

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound thirty SimpleOS emulated-device input to framebuffer pairs")
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

- should validate every physical scale and viewport matrix row
   - Artifact capture: after_step
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

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate every physical scale and viewport matrix row")
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

- should reject every performance budget breach
   - Log capture: after_step
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject every performance budget breach")
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

- should reject silent unrequested or misclassified fallback rows
   - Log capture: after_step
- Submit accelerated rows that silently use fallback or omit typed fallback evidence
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: submit_invalid_performance_evidence("silent-fallback") equals `rejected`
   - Expected: submit_invalid_performance_evidence("unrequested-fallback") equals `rejected`
   - Expected: submit_invalid_performance_evidence("fallback-without-accelerated-failure") equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject silent unrequested or misclassified fallback rows")
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

- should reject stale incomplete fabricated or nonproduction rows
   - Artifact capture: after_step
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject stale incomplete fabricated or nonproduction rows")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b3f945abb821315509c4901a18111c056eaab0daa94563c657739c60ece6812`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b3f945abb821315509c4901a18111c056eaab0daa94563c657739c60ece6812`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b3f945abb821315509c4901a18111c056eaab0daa94563c657739c60ece6812`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/wm/simple_wm_performance_spec.spl
mirror: doc/06_spec/03_system/os/wm/simple_wm_performance_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/wm/simple_wm_performance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/simple_wm_performance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/simple_wm_performance_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should measure ten warm production host launches after one discarded launch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_performance_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should measure ten warm production host launches after one discarded launch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_performance_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound thirty acknowledged host fullscreen mode pairs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_performance_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bound thirty acknowledged host fullscreen mode pairs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_performance_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound six hundred accelerated frame durations after sixty discarded frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_performance_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bound six hundred accelerated frame durations after sixty discarded frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/wm/simple_wm_performance_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound an explicitly requested typed fallback frame row' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_performance_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound final RSS and final-fifty slope after one hundred host mode pairs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/wm/simple_wm_performance_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound thirty SimpleOS emulated-device input to framebuffer pairs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
