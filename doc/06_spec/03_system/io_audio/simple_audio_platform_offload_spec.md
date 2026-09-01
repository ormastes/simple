# simple_audio_platform_offload_spec

> Native platform devices and optional audio offload preserve realtime CPU semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_platform_offload_spec

Native platform devices and optional audio offload preserve realtime CPU semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_platform_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native platform devices and optional audio offload preserve realtime CPU semantics.

## Scenarios

### Native pure-Simple audio and offload

#### reports an unbound native backend without claiming vendor ownership

- reports an unbound native backend without claiming vendor ownership
   - Log capture: after_step
- Bind the exact pure-Simple artifact
   - Log capture: after_step
- Inspect backend and device capabilities
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: linux.status equals `unavailable`
   - Expected: linux.owner equals `pure-simple-contract`
   - Expected: linux.vendor_audio_engine is false
- Open and negotiate the playback and capture stream
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: linux.playback equals `closed`
   - Expected: linux.capture equals `closed`
   - Expected: linux.period_ms equals `0`
- Drain cancel and shut down
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: linux.live_resources equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports an unbound native backend without claiming vendor ownership")
step("Bind the exact pure-Simple artifact")
val linux = check_simple_audio_backend("linux", "pipewire")
step("Inspect backend and device capabilities")
expect(linux.status).to_equal("unavailable")
expect(linux.owner).to_equal("pure-simple-contract")
expect(linux.vendor_audio_engine).to_equal(false)
step("Open and negotiate the playback and capture stream")
expect(linux.playback).to_equal("closed")
expect(linux.capture).to_equal("closed")
expect(linux.period_ms).to_equal(0)
step("Drain cancel and shut down")
expect(linux.live_resources).to_equal(0)
```

</details>

#### preserves CPU semantics for prewarmed coarse offload

- preserves CPU semantics for prewarmed coarse offload
   - Log capture: after_step
- Route direct 2D and 3D sources through one graph
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: parity.metadata_exact is true
- Enable prewarmed audio offload
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: result.callback_owned_by_cpu is true
   - Expected: result.final_output_owned_by_cpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves CPU semantics for prewarmed coarse offload")
step("Route direct 2D and 3D sources through one graph")
val parity = check_spatial_audio_parity()
expect(parity.metadata_exact).to_equal(true)
expect(parity.max_sample_error_ppm).to_be_less_than(11)
step("Enable prewarmed audio offload")
val result = check_audio_offload_fallback("vulkan")
expect(result.operations).to_contain("partitioned-convolution")
expect(result.operations).to_contain("hrtf-filter-bank")
expect(result.operations).to_contain("long-reverb")
expect(result.operations).to_contain("ambisonics")
expect(result.callback_owned_by_cpu).to_equal(true)
expect(result.final_output_owned_by_cpu).to_equal(true)
expect(result.deadline_period_percent).to_be_less_than(61)
```

</details>

<details>
<summary>Advanced: falls back before the next period after timeout rejection and device loss</summary>

#### falls back before the next period after timeout rejection and device loss

- falls back before the next period after timeout rejection and device loss
- Force timeout device loss rejection and queue pressure
   - Expected: result.timeout_fallback equals `cpu-next-period`
   - Expected: result.device_lost_fallback equals `cpu-next-period`
   - Expected: result.rejected_fallback equals `cpu-next-period`
   - Expected: result.queue_full_fallback equals `cpu-next-period`
- Observe correlated fallback events and continuous output
   - Expected: result.output_gaps equals `0`
   - Expected: result.late_results_committed equals `0`
   - Expected: result.live_tokens equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back before the next period after timeout rejection and device loss")
step("Force timeout device loss rejection and queue pressure")
val result = check_audio_offload_fallback("faults")
expect(result.timeout_fallback).to_equal("cpu-next-period")
expect(result.device_lost_fallback).to_equal("cpu-next-period")
expect(result.rejected_fallback).to_equal("cpu-next-period")
expect(result.queue_full_fallback).to_equal("cpu-next-period")
step("Observe correlated fallback events and continuous output")
expect(result.output_gaps).to_equal(0)
expect(result.late_results_committed).to_equal(0)
expect(result.live_tokens).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: keeps missing Linux macOS Windows and BSD evidence explicit</summary>

#### keeps missing Linux macOS Windows and BSD evidence explicit

- keeps missing Linux macOS Windows and BSD evidence explicit
   - Log capture: after_step
- Inspect the platform capability matrix without cross-host inference
   - Log capture: after_step
   - Evidence: log output verified by 6 expected checks
   - Expected: matrix.linux equals `unavailable`
   - Expected: matrix.macos equals `unavailable`
   - Expected: matrix.windows equals `unavailable`
   - Expected: matrix.openbsd equals `unavailable`
   - Expected: matrix.freebsd equals `unavailable`
   - Expected: matrix.netbsd equals `unavailable`
- Refuse to fabricate NFR latency coverage or provenance
   - Log capture: after_step
   - Evidence: log output verified by 6 expected checks
   - Expected: matrix.event_p95_us equals `0`
   - Expected: matrix.event_p99_us equals `0`
   - Expected: matrix.underruns_30m equals `0`
   - Expected: matrix.branch_coverage_percent equals `0`
   - Expected: matrix.callback_forbidden_actions equals `0`
   - Expected: matrix.provenance_status equals `missing-native-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps missing Linux macOS Windows and BSD evidence explicit")
step("Inspect the platform capability matrix without cross-host inference")
val matrix = check_io_audio_platform_matrix()
expect(matrix.linux).to_equal("unavailable")
expect(matrix.macos).to_equal("unavailable")
expect(matrix.windows).to_equal("unavailable")
expect(matrix.openbsd).to_equal("unavailable")
expect(matrix.freebsd).to_equal("unavailable")
expect(matrix.netbsd).to_equal("unavailable")
step("Refuse to fabricate NFR latency coverage or provenance")
expect(matrix.event_p95_us).to_equal(0)
expect(matrix.event_p99_us).to_equal(0)
expect(matrix.underruns_30m).to_equal(0)
expect(matrix.audio_rss_mib).to_be_less_than(49)
expect(matrix.branch_coverage_percent).to_equal(0)
expect(matrix.callback_forbidden_actions).to_equal(0)
expect(matrix.provenance_status).to_equal("missing-native-evidence")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-011`
- `REQ-012`
- `REQ-013`
- `REQ-014`
- `REQ-015`
- `REQ-016`
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7c390e901d4f77cb71626e9b630ff136033b1ee2bb0e78de11695dcd2d9cd61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7c390e901d4f77cb71626e9b630ff136033b1ee2bb0e78de11695dcd2d9cd61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7c390e901d4f77cb71626e9b630ff136033b1ee2bb0e78de11695dcd2d9cd61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_platform_offload_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_platform_offload_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_platform_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_platform_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_platform_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_platform_offload_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 11 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_platform_offload_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an unbound native backend without claiming vendor ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_platform_offload_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves CPU semantics for prewarmed coarse offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_platform_offload_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back before the next period after timeout rejection and device loss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
