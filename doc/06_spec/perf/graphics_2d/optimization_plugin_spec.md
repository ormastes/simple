# Optimization Plugin Specification

> Tests covering optimization_plugin — AC-10: provider hit/change metadata, provider name constants, provider event structure, ProviderReport accumulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimization Plugin Specification

## Scenarios

### optimization_plugin — AC-10: provider hit/change metadata

### provider name constants

#### AC-10: auto_vectorize provider name is correct

- verify auto_vectorize provider name is correct
   - Expected: PROVIDER_AUTO_VECTORIZE equals `auto_vectorize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify auto_vectorize provider name is correct")
expect(PROVIDER_AUTO_VECTORIZE).to_equal("auto_vectorize")
```

</details>

#### AC-10: simd_lowering provider name is correct

- verify simd_lowering provider name is correct
   - Expected: PROVIDER_SIMD_LOWERING equals `simd_lowering`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify simd_lowering provider name is correct")
expect(PROVIDER_SIMD_LOWERING).to_equal("simd_lowering")
```

</details>

#### AC-10: two optimization providers are defined

- verify two optimization providers are defined
   - Expected: providers.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify two optimization providers are defined")
val providers: [text] = [PROVIDER_AUTO_VECTORIZE, PROVIDER_SIMD_LOWERING]
expect(providers.len()).to_equal(2)
```

</details>

### provider event structure

#### AC-10: event carries kernel_id field

- verify event carries kernel_id field
   - Expected: e.kernel_id equals `fill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify event carries kernel_id field")
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.kernel_id).to_equal("fill")
```

</details>

#### AC-10: event carries changed field

- verify event carries changed field
   - Expected: e.changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify event carries changed field")
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.changed).to_equal(true)
```

</details>

#### AC-10: event carries provider field

- verify event carries provider field
   - Expected: e.provider equals `PROVIDER_AUTO_VECTORIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify event carries provider field")
val e: ProviderEventSentinel = make_provider_event("fill", true, PROVIDER_AUTO_VECTORIZE)
expect(e.provider).to_equal(PROVIDER_AUTO_VECTORIZE)
```

</details>

#### AC-10: unchanged event has changed == false

- verify unchanged event has changed == false
   - Expected: e.changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify unchanged event has changed == false")
val e: ProviderEventSentinel = make_provider_event("alpha_blend", false, PROVIDER_AUTO_VECTORIZE)
expect(e.changed).to_equal(false)
```

</details>

### ProviderReport accumulation

#### AC-10: report frame_id is greater than zero

- verify report frame_id is greater than zero
   - Expected: r.frame_id > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify report frame_id is greater than zero")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.frame_id > 0).to_equal(true)
```

</details>

#### AC-10: active_providers contains auto_vectorize

- verify active_providers contains auto_vectorize
   - Expected: r.active_providers[0] equals `PROVIDER_AUTO_VECTORIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify active_providers contains auto_vectorize")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.active_providers[0]).to_equal(PROVIDER_AUTO_VECTORIZE)
```

</details>

#### AC-10: active_providers contains simd_lowering

- verify active_providers contains simd_lowering
   - Expected: r.active_providers[1] equals `PROVIDER_SIMD_LOWERING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify active_providers contains simd_lowering")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.active_providers[1]).to_equal(PROVIDER_SIMD_LOWERING)
```

</details>

#### AC-10: five events are recorded in one frame

- verify five events are recorded in one frame
   - Expected: r.events.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify five events are recorded in one frame")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.events.len()).to_equal(5)
```

</details>

#### AC-10: total_hits is greater than zero after a frame

- verify total_hits is greater than zero after a frame
   - Expected: r.total_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify total_hits is greater than zero after a frame")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.total_hits > 0).to_equal(true)
```

</details>

#### AC-10: total_changes matches events with changed == true

- verify total_changes matches events with changed == true
   - Expected: counted equals `r.total_changes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify total_changes matches events with changed == true")
val r: ProviderReportSentinel = make_provider_report_ok()
val counted: i64 = count_changes(r)
expect(counted).to_equal(r.total_changes)
```

</details>

#### AC-10: total_changes is less than or equal to total_hits

- verify total_changes is less than or equal to total_hits
   - Expected: r.total_changes <= r.total_hits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-OPT-PLUGIN
step("verify total_changes is less than or equal to total_hits")
val r: ProviderReportSentinel = make_provider_report_ok()
expect(r.total_changes <= r.total_hits).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/graphics_2d/optimization_plugin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering optimization_plugin — AC-10: provider hit/change metadata, provider name constants, provider event structure, ProviderReport accumulation.
- optimization_plugin — AC-10: provider hit/change metadata
- provider name constants
- provider event structure
- ProviderReport accumulation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-OPT-PLUGIN`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b330f03ae121a44c2293a780d3f717b98d09a7e0decb31aa9947c1cf22aa3f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b330f03ae121a44c2293a780d3f717b98d09a7e0decb31aa9947c1cf22aa3f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b330f03ae121a44c2293a780d3f717b98d09a7e0decb31aa9947c1cf22aa3f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/perf/graphics_2d/optimization_plugin_spec.spl
mirror: doc/06_spec/perf/graphics_2d/optimization_plugin_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/graphics_2d/optimization_plugin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/graphics_2d/optimization_plugin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/graphics_2d/optimization_plugin_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/graphics_2d/optimization_plugin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/graphics_2d/optimization_plugin_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: auto_vectorize provider name is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/optimization_plugin_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: simd_lowering provider name is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/optimization_plugin_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-10: two optimization providers are defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
