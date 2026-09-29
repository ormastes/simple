# audio_pitch_contract_spec

> Purpose: Prove live audio pitch fails closed before and across its raw SFFI boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audio_pitch_contract_spec

Purpose: Prove live audio pitch fails closed before and across its raw SFFI boundary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove live audio pitch fails closed before and across its raw SFFI boundary.
Audience: runtime and audio maintainers.

## Scenarios

### audio pitch SFFI contract

#### rejects an invalid generation handle

- rejects an invalid generation handle
- Call the safe pitch wrapper with an invalid playback handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an invalid generation handle")
step("Call the safe pitch wrapper with an invalid playback handle")
expect_not audio_set_pitch(0, 1.0)
```

</details>

#### rejects non-positive pitch before the foreign call

- rejects non-positive pitch before the foreign call
- Call the safe pitch wrapper with an invalid pitch multiplier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-positive pitch before the foreign call")
step("Call the safe pitch wrapper with an invalid pitch multiplier")
expect_not audio_set_pitch(1, 0.0)
expect_not audio_set_pitch(1, -1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SFFI-AUDIO-PITCH-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b630838352bf777c08558c3c50ed555decfc9a20b73aad45c8a696ba48b5e736`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b630838352bf777c08558c3c50ed555decfc9a20b73aad45c8a696ba48b5e736`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b630838352bf777c08558c3c50ed555decfc9a20b73aad45c8a696ba48b5e736`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid generation handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/audio_effects/audio_pitch_contract_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-positive pitch before the foreign call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
