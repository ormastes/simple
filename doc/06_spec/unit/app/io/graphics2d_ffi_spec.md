# Graphics2d Ffi Specification

> Tests covering graphics2d FFI compatibility facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graphics2d Ffi Specification

## Scenarios

### graphics2d FFI compatibility facade

#### contains no duplicate foreign declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains no duplicate foreign declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains no duplicate foreign declarations")
val source = file_read("src/app/io/graphics2d_ffi.spl")
assert_equal(source.contains("extern fn "), false)
assert_equal(source.contains("@extern("), false)
```

</details>

#### exports the canonical safe graphics surface explicitly

- exports the canonical safe graphics surface explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports the canonical safe graphics surface explicitly")
val source = file_read("src/app/io/graphics2d_ffi.spl")
assert_contains(source, "export use app.io.graphics2d_sffi.{{")
assert_equal(source.contains("graphics_path_builder_new"), true)
assert_equal(source.contains("graphics_path_transform"), true)
assert_equal(source.contains("graphics2d_sffi.*"), false)
```

</details>

#### does not re-export raw runtime symbols

- does not re-export raw runtime symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not re-export raw runtime symbols")
val source = file_read("src/app/io/graphics2d_ffi.spl")
assert_equal(source.contains("rt_lyon_"), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/io/graphics2d_ffi_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering graphics2d FFI compatibility facade.
- graphics2d FFI compatibility facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fa4c5709ab00cc6ead3eff632e914d917daca9897e94ae282dbec320013fa48`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fa4c5709ab00cc6ead3eff632e914d917daca9897e94ae282dbec320013fa48`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fa4c5709ab00cc6ead3eff632e914d917daca9897e94ae282dbec320013fa48`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/app/io/graphics2d_ffi_spec.spl
mirror: doc/06_spec/unit/app/io/graphics2d_ffi_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/io/graphics2d_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/io/graphics2d_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/io/graphics2d_ffi_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/app/io/graphics2d_ffi_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains no duplicate foreign declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/io/graphics2d_ffi_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports the canonical safe graphics surface explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/io/graphics2d_ffi_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not re-export raw runtime symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
