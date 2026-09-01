# Wire Golden Specification

> Tests covering UI wire-protocol golden bytes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wire Golden Specification

## Scenarios

### UI wire-protocol golden bytes

#### encodes empty snapshot byte-identically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes empty snapshot byte-identically
   - Expected: out equals `GOLDEN_EMPTY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty snapshot byte-identically")
val out = ui_access_snapshot_to_json(_empty_snapshot())
expect(out).to_equal(GOLDEN_EMPTY)
```

</details>

#### encodes single-panel snapshot byte-identically

- encodes single-panel snapshot byte-identically
   - Expected: out equals `GOLDEN_SINGLE_PANEL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes single-panel snapshot byte-identically")
val out = ui_access_snapshot_to_json(_single_panel_snapshot())
expect(out).to_equal(GOLDEN_SINGLE_PANEL)
```

</details>

#### encodes multi-widget snapshot byte-identically

- encodes multi-widget snapshot byte-identically
   - Expected: out equals `GOLDEN_MULTI_WIDGET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes multi-widget snapshot byte-identically")
val out = ui_access_snapshot_to_json(_multi_widget_snapshot())
expect(out).to_equal(GOLDEN_MULTI_WIDGET)
```

</details>

#### freezes UI_ACCESS_PROTOCOL_VERSION at v1

- freezes UI_ACCESS_PROTOCOL_VERSION at v1
   - Expected: UI_ACCESS_PROTOCOL_VERSION equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes UI_ACCESS_PROTOCOL_VERSION at v1")
expect(UI_ACCESS_PROTOCOL_VERSION).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/wire_golden/wire_golden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UI wire-protocol golden bytes.
- UI wire-protocol golden bytes

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `389b938d0b979d9641dcf8a6a93c0037b88405efd3a580fc7681d537512a1a47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `389b938d0b979d9641dcf8a6a93c0037b88405efd3a580fc7681d537512a1a47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `389b938d0b979d9641dcf8a6a93c0037b88405efd3a580fc7681d537512a1a47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/ui/wire_golden/wire_golden_spec.spl
mirror: doc/06_spec/unit/app/ui/wire_golden/wire_golden_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/wire_golden/wire_golden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/wire_golden/wire_golden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/wire_golden/wire_golden_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/wire_golden/wire_golden_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes empty snapshot byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/wire_golden/wire_golden_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes single-panel snapshot byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/wire_golden/wire_golden_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes multi-widget snapshot byte-identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
