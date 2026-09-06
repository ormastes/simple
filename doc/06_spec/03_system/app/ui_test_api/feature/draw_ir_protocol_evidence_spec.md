# Draw IR Protocol Evidence

> Captures real UI test API Draw IR Protocol-v2 layout and diff responses through `handle_test_request`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw IR Protocol Evidence

Captures real UI test API Draw IR Protocol-v2 layout and diff responses through `handle_test_request`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/03_plan/sys_test/draw_ir_protocol_evidence.md |
| Plan | doc/03_plan/sys_test/draw_ir_protocol_evidence.md |
| Design | doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md |
| Source | `test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Captures real UI test API Draw IR Protocol-v2 layout and diff responses through
`handle_test_request`.

**Requirements:** doc/03_plan/sys_test/draw_ir_protocol_evidence.md
**Plan:** doc/03_plan/sys_test/draw_ir_protocol_evidence.md
**Design:** doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md
**Artifacts:** build/test-artifacts/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence/draw_ir_protocol.json

## Syntax

The spec calls the UI test API handler directly and writes the protocol output
that a test client would inspect.

## Evidence

Display policy: `links`

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `draw_ir_protocol.json` | JSON artifact | `build/test-artifacts/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence/draw_ir_protocol.json` |

## Scenarios

### Draw IR protocol evidence

#### captures layout geometry and baseline diff protocol output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures layout geometry and baseline diff protocol output
   - Expected: layout_status equals `200`
   - Expected: layout_ctype equals `application/vnd.simple.draw-ir+json`
   - Expected: current_status equals `200`
   - Expected: empty_status equals `200`
   - Expected: _write_capture(capture) equals `0`
   - Expected: _capture_file_state(capture) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures layout geometry and baseline diff protocol output")
val state = _make_state()
val (layout_status, layout_ctype, layout_body) = handle_test_request(
    "/api/test/draw-ir/layout?id=root&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)
val (current_status, current_ctype, current_body) = handle_test_request(
    "/api/test/draw-ir/diff?baseline=current&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)
val (empty_status, empty_ctype, empty_body) = handle_test_request(
    "/api/test/draw-ir/diff?baseline=empty&capability=draw_ir",
    "GET",
    "",
    state,
    _noop_inject,
    nil
)

expect(layout_status).to_equal(200)
expect(layout_ctype).to_equal("application/vnd.simple.draw-ir+json")
expect(layout_body).to_contain("\"id\":\"root\"")
expect(layout_body).to_contain("\"geometry\"")
expect(layout_body).to_contain("\"hit_rect\"")
expect(layout_body).to_contain("\"computed_style\"")
expect(current_status).to_equal(200)
expect(current_body).to_contain("\"mode\":\"baseline\"")
expect(current_body).to_contain("\"changed_count\":0")
expect(empty_status).to_equal(200)
expect(empty_body).to_contain("\"state\":\"added\"")

val capture = "[\n" +
    _protocol_record("layout", layout_status, layout_ctype, layout_body) + ",\n" +
    _protocol_record("baseline_current", current_status, current_ctype, current_body) + ",\n" +
    _protocol_record("baseline_empty", empty_status, empty_ctype, empty_body) + "\n]"
expect(_write_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/draw_ir_protocol_evidence.md`
- **Plan:** `doc/03_plan/sys_test/draw_ir_protocol_evidence.md`
- **Design:** `doc/05_design/app/ui_test_api/draw_ir_protocol_evidence.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d4b52f4055b73db8e1912d7fa17f6bd463b03ba88285a70616d778e1bbb3acc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d4b52f4055b73db8e1912d7fa17f6bd463b03ba88285a70616d778e1bbb3acc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d4b52f4055b73db8e1912d7fa17f6bd463b03ba88285a70616d778e1bbb3acc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl
mirror: doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
