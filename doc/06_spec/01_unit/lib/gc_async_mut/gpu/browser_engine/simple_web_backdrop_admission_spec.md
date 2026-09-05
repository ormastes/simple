# Simple Web Backdrop Admission Specification

> Tests covering Simple Web backdrop material admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Backdrop Admission Specification

## Scenarios

### Simple Web backdrop material admission

#### admits the canonical Aetheric WM backdrop without runtime text predicates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits the canonical Aetheric WM backdrop without runtime text predicates
   - Expected: receipt.realized_blur_px equals `4`
   - Expected: receipt.realized_saturation_milli equals `1700`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits the canonical Aetheric WM backdrop without runtime text predicates")
# Build the value at runtime so this exercises held text receivers,
# matching the computed-style value used by the freestanding WM.
val backdrop = ["blur(30px)", "saturate(170%)"].join(" ")
val receipt = simple_web_backdrop_admission(backdrop)
expect(receipt.admitted).to_be(true)
expect(receipt.realized_blur_px).to_equal(4)
expect(receipt.realized_saturation_milli).to_equal(1700)
```

</details>

#### fails closed on malformed units, suffixes, and extra terms

- fails closed on malformed units, suffixes, and extra terms


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on malformed units, suffixes, and extra terms")
expect(simple_web_backdrop_admission("blur(30) saturate(170%)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(30px) saturate(170)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(30px) saturate(170%) extra").admitted).to_be(false)
```

</details>

#### fails closed on empty, signed, embedded, and overflowing decimals

- fails closed on empty, signed, embedded, and overflowing decimals


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on empty, signed, embedded, and overflowing decimals")
expect(simple_web_backdrop_admission("blur(px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(+30px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(030px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(3x0px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(1000001px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(999999999999999999999999px)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(30px) saturate(301%)").admitted).to_be(false)
expect(simple_web_backdrop_admission("blur(30px) saturate(999999999999999999999999%)").admitted).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Web backdrop material admission.
- Simple Web backdrop material admission

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

- Canonical SPipe generation for source `72e327fcfab037b01d0c947e5330fc2835b24427e5e0f86fe9096c2025f8608b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `72e327fcfab037b01d0c947e5330fc2835b24427e5e0f86fe9096c2025f8608b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `72e327fcfab037b01d0c947e5330fc2835b24427e5e0f86fe9096c2025f8608b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the canonical Aetheric WM backdrop without runtime text predicates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on malformed units, suffixes, and extra terms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_backdrop_admission_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on empty, signed, embedded, and overflowing decimals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
