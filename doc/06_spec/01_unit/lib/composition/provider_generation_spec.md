# Provider Generation Specification

> Tests covering provider generation activation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Generation Specification

## Scenarios

### provider generation activation

#### validates before mutation and preserves the active generation on failure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates before mutation and preserves the active generation on failure
   - Expected: first.status equals `SIMPLE_GENERATION_OK`
   - Expected: failed.status equals `SIMPLE_GENERATION_DIGEST_MISMATCH`
   - Expected: pin.generation equals `first.generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates before mutation and preserves the active generation on failure")
val manager = ProviderGenerationManagerV1.create()
val first = provider_generation_activate_v1(manager, candidate_v1())
expect(first.status).to_equal(SIMPLE_GENERATION_OK)
var denied = candidate_v1(202)
denied.artifact_digest = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
val failed = provider_generation_activate_v1(manager, denied)
expect(failed.status).to_equal(SIMPLE_GENERATION_DIGEST_MISMATCH)
val pin = provider_generation_pin_active_v1(manager, 41)
expect(pin.generation).to_equal(first.generation)
```

</details>

#### keeps a retired generation available while its handle is pinned

- keeps a retired generation available while its handle is pinned
   - Expected: old_pin.pin_id == second_old_pin.pin_id is false
   - Expected: second.previous_generation equals `first.generation`
   - Expected: second.generation == first.generation is false
   - Expected: provider_generation_available_v1(manager, 41, first.generation) is true
   - Expected: provider_generation_sweep_v1(manager) equals `0`
   - Expected: provider_generation_release_v1(manager, old_pin) equals `SIMPLE_GENERATION_OK`
   - Expected: provider_generation_sweep_v1(manager) equals `0`
   - Expected: provider_generation_release_v1(manager, second_old_pin) equals `SIMPLE_GENERATION_OK`
   - Expected: provider_generation_sweep_v1(manager) equals `1`
   - Expected: provider_generation_available_v1(manager, 41, first.generation) is false
   - Expected: provider_generation_available_v1(manager, 41, second.generation) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a retired generation available while its handle is pinned")
val manager = ProviderGenerationManagerV1.create()
val first = provider_generation_activate_v1(manager, candidate_v1())
val old_pin = provider_generation_pin_active_v1(manager, 41)
val second_old_pin = provider_generation_pin_active_v1(manager, 41)
expect(old_pin.pin_id == second_old_pin.pin_id).to_equal(false)
val second = provider_generation_activate_v1(manager, candidate_v1(202))
expect(second.previous_generation).to_equal(first.generation)
expect(second.generation == first.generation).to_equal(false)
expect(provider_generation_available_v1(manager, 41, first.generation)).to_equal(true)
expect(provider_generation_sweep_v1(manager)).to_equal(0)
expect(provider_generation_release_v1(manager, old_pin)).to_equal(SIMPLE_GENERATION_OK)
expect(provider_generation_sweep_v1(manager)).to_equal(0)
expect(provider_generation_release_v1(manager, second_old_pin)).to_equal(SIMPLE_GENERATION_OK)
expect(provider_generation_sweep_v1(manager)).to_equal(1)
expect(provider_generation_available_v1(manager, 41, first.generation)).to_equal(false)
expect(provider_generation_available_v1(manager, 41, second.generation)).to_equal(true)
```

</details>

#### rejects non-callable candidates and unknown or duplicate releases

- rejects non-callable candidates and unknown or duplicate releases
   - Expected: provider_generation_activate_v1(manager, denied).status equals `SIMPLE_GENERATION_ADMISSION_REQUIRED`
   - Expected: provider_generation_pin_active_v1(manager, 41).status equals `SIMPLE_GENERATION_NOT_ACTIVE`
   - Expected: active.status equals `SIMPLE_GENERATION_OK`
   - Expected: provider_generation_release_v1(manager, pin) equals `SIMPLE_GENERATION_OK`
   - Expected: provider_generation_release_v1(manager, pin) equals `SIMPLE_GENERATION_PIN_UNKNOWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-callable candidates and unknown or duplicate releases")
val manager = ProviderGenerationManagerV1.create()
var denied = candidate_v1()
denied.process_callable = false
expect(provider_generation_activate_v1(manager, denied).status).to_equal(SIMPLE_GENERATION_ADMISSION_REQUIRED)
expect(provider_generation_pin_active_v1(manager, 41).status).to_equal(SIMPLE_GENERATION_NOT_ACTIVE)
val active = provider_generation_activate_v1(manager, candidate_v1())
val pin = provider_generation_pin_active_v1(manager, 41)
expect(active.status).to_equal(SIMPLE_GENERATION_OK)
expect(provider_generation_release_v1(manager, pin)).to_equal(SIMPLE_GENERATION_OK)
expect(provider_generation_release_v1(manager, pin)).to_equal(SIMPLE_GENERATION_PIN_UNKNOWN)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/composition/provider_generation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering provider generation activation.
- provider generation activation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `004082913d239e97fc2b538428c1e83a7bba41b8f132b104b1c6df76dd8a74ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `004082913d239e97fc2b538428c1e83a7bba41b8f132b104b1c6df76dd8a74ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `004082913d239e97fc2b538428c1e83a7bba41b8f132b104b1c6df76dd8a74ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/composition/provider_generation_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/provider_generation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/provider_generation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/provider_generation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/provider_generation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/composition/provider_generation_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates before mutation and preserves the active generation on failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/provider_generation_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a retired generation available while its handle is pinned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/provider_generation_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-callable candidates and unknown or duplicate releases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
