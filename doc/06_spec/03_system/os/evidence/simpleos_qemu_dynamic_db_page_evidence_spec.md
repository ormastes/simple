# SimpleOS dynamic database page evidence

> The in-process branch executes the same `SimpleDbService` request owner used by the boot HTTP listener. The optional live branch boots the current-source RV64 kernel through `qemu_rv64_http_test.shs`; that runner now requires the complete GET /db, create, insert, select, refreshed GET sequence before it passes. Missing live prerequisites publish an exact blocker and resume command.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS dynamic database page evidence

The in-process branch executes the same `SimpleDbService` request owner used by the boot HTTP listener. The optional live branch boots the current-source RV64 kernel through `qemu_rv64_http_test.shs`; that runner now requires the complete GET /db, create, insert, select, refreshed GET sequence before it passes. Missing live prerequisites publish an exact blocker and resume command.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/evidence/simpleos_qemu_dynamic_db_page_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The in-process branch executes the same `SimpleDbService` request owner used by
the boot HTTP listener. The optional live branch boots the current-source RV64
kernel through `qemu_rv64_http_test.shs`; that runner now requires the complete
GET /db, create, insert, select, refreshed GET sequence before it passes.
Missing live prerequisites publish an exact blocker and resume command.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run the spec for the in-process request flow. For QEMU evidence, build the RV64
kernel, set `SIMPLE_EVIDENCE_SIMPLEOS_DYNAMIC_DB=1`, rerun it, and review the
captured page plus create, insert, select, and refreshed GET sequence.

## Scenarios

### REQ-EVS-012 SimpleOS dynamic database page evidence

#### boots or blocks exactly and proves insert query and refreshed HTML

- Capture the feature evidence
- var db = SimpleDbService new
- Verify the structured evidence
   - Expected: initial_page.find("<td>hello</td>") equals `-1`
- verify live capture or blocker
- Render the evidence for review
- Publish the showcase link
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: publication equals `DYNAMIC_DB_PAGE_LOG`
   - Expected: publication equals `blocked-contract`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
var db = SimpleDbService.new()
val initial_page = db.execute_http_request(
    "GET /db HTTP/1.1\r\nHost: simpleos\r\n\r\n"
)
val create = db.execute_http_request(
    "POST /db HTTP/1.1\r\n\r\nCREATE showcase"
)
val insert = db.execute_http_request(
    "POST /db HTTP/1.1\r\n\r\nINSERT showcase greeting hello"
)
val query = db.execute_http_request(
    "POST /db HTTP/1.1\r\n\r\nSELECT showcase greeting"
)
val refreshed_page = db.execute_http_request(
    "GET /db HTTP/1.1\r\nHost: simpleos\r\n\r\n"
)
val live = capture_live_dynamic_db_page()

step("Verify the structured evidence")
expect(initial_page).to_start_with("HTTP/1.1 200 OK")
expect(initial_page).to_contain(
    "Content-Type: text/html; charset=utf-8"
)
expect(initial_page).to_contain("<h1>SimpleOS DB</h1>")
expect(initial_page).to_contain("<table>")
expect(initial_page.find("<td>hello</td>")).to_equal(-1)
expect(create).to_end_with("\r\n\r\nOK CREATE")
expect(insert).to_end_with("\r\n\r\nOK INSERT")
expect(query).to_end_with("\r\n\r\nhello")
expect(refreshed_page).to_start_with("HTTP/1.1 200 OK")
expect(refreshed_page).to_contain("<td>showcase</td>")
expect(refreshed_page).to_contain("<td>greeting</td>")
expect(refreshed_page).to_contain("<td>hello</td>")
verify_live_capture_or_blocker(live)

step("Render the evidence for review")
expect(refreshed_page).to_contain(
    "<tr><td>showcase</td><td>greeting</td><td>hello</td></tr>"
)
val rendered = (
    "live_status: " + live.status + "\n" +
    "reason: " + live.reason + "\n" +
    "resume: " + live.resume_command
)
expect(rendered).to_contain("live_status: " + live.status)

step("Publish the showcase link")
val publication = if live.status == "captured":
    DYNAMIC_DB_PAGE_LOG
else:
    "blocked-contract"
if live.status == "captured":
    expect(publication).to_equal(DYNAMIC_DB_PAGE_LOG)
else:
    expect(publication).to_equal("blocked-contract")
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

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
