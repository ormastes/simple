# Access Cli Specification

> Tests covering simple ui access CLI adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Cli Specification

## Scenarios

### simple ui access CLI adapter

#### routes UI backends to the deployed compiled sibling

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes UI backends to the deployed compiled sibling
   - Expected: ui_backend_binary_for_runtime("/opt/simple/bin/simple") equals `/opt/simple/bin/simple_ui_backend`
   - Expected: ui_backend_binary_for_runtime("simple.exe") equals `simple_ui_backend.exe`
   - Expected: ui_backend_binary_for_runtime("C:\\Simple\\simple.exe") equals `C:\\Simple\\simple_ui_backend.exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes UI backends to the deployed compiled sibling")
expect(ui_backend_binary_for_runtime("/opt/simple/bin/simple")).to_equal("/opt/simple/bin/simple_ui_backend")
expect(ui_backend_binary_for_runtime("simple.exe")).to_equal("simple_ui_backend.exe")
expect(ui_backend_binary_for_runtime("C:\\Simple\\simple.exe")).to_equal("C:\\Simple\\simple_ui_backend.exe")
```

</details>

#### registers the six T32-style operations through shared descriptors

- registers the six T32-style operations through shared descriptors
   - Expected: descriptors.len() equals `6`
   - Expected: descriptors[0].name equals `windows`
   - Expected: descriptors[0].operation equals `list`
   - Expected: descriptors[0].safety.read_only is true
   - Expected: descriptors[4].name equals `act`
   - Expected: descriptors[4].operation equals `act`
   - Expected: descriptors[4].safety.read_only is false
   - Expected: descriptors[5].operation equals `history`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("registers the six T32-style operations through shared descriptors")
val descriptors = ui_access_cli_descriptors()
expect(descriptors.len()).to_equal(6)
expect(descriptors[0].name).to_equal("windows")
expect(descriptors[0].operation).to_equal("list")
expect(descriptors[0].safety.read_only).to_equal(true)
expect(descriptors[4].name).to_equal("act")
expect(descriptors[4].operation).to_equal("act")
expect(descriptors[4].safety.read_only).to_equal(false)
expect(descriptors[5].operation).to_equal("history")
```

</details>

#### maps reads to the existing UI test API with encoded selectors

- maps reads to the existing UI test API with encoded selectors
   - Expected: ui_access_cli_route(snapshot)? equals `/api/test/ui/snapshot`
   - Expected: ui_access_cli_route(surface)? equals `/api/test/ui/surface?id=main%20pane`
   - Expected: ui_access_cli_route(history)? equals `/api/test/ui/history?surface_id=main&count=10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps reads to the existing UI test API with encoded selectors")
val snapshot = ui_access_cli_parse_request(["snapshot", "--json"])?
expect(ui_access_cli_route(snapshot)?).to_equal("/api/test/ui/snapshot")
val surface = ui_access_cli_parse_request(["surface", "main pane", "--json"])?
expect(ui_access_cli_route(surface)?).to_equal("/api/test/ui/surface?id=main%20pane")
val find = ui_access_cli_parse_request(["find", "--surface", "main", "--kind", "button", "--text", "Build now", "--limit", "20"])?
val find_route = ui_access_cli_route(find)?
expect(find_route).to_start_with("/api/test/ui/query?")
expect(find_route).to_contain("surface_id=main")
expect(find_route).to_contain("kind=button")
expect(find_route).to_contain("text=Build%20now")
expect(find_route).to_contain("limit=20")
val history = ui_access_cli_parse_request(["history", "--surface", "main", "--count", "10"])?
expect(ui_access_cli_route(history)?).to_equal("/api/test/ui/history?surface_id=main&count=10")
```

</details>

#### validates and serializes one semantic action without raw input fallback

- validates and serializes one semantic action without raw input fallback
   - Expected: request.timeout_ms equals `2000`
   - Expected: request.output_mode equals `json`
   - Expected: ui_access_cli_route(request)? equals `/api/test/ui/act`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("validates and serializes one semantic action without raw input fallback")
val request = ui_access_cli_parse_request(["act", "--canonical", "main#build", "--action", "click", "--revision", "42", "--timeout", "2000", "--json"])?
expect(request.timeout_ms).to_equal(2000)
expect(request.output_mode).to_equal("json")
expect(ui_access_cli_route(request)?).to_equal("/api/test/ui/act")
val body = ui_access_cli_action_body(request, "act-7")
expect(body).to_contain("\"canonical_id\":\"main#build\"")
expect(body).to_contain("\"action\":\"click\"")
expect(body).to_contain("\"request_id\":\"act-7\"")
expect(body).to_contain("\"expected_revision\":42")
```

</details>

#### rejects invalid action targets and unbounded numeric options

- rejects invalid action targets and unbounded numeric options


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects invalid action targets and unbounded numeric options")
match ui_access_cli_parse_request(["act", "--canonical", "build", "--action", "click"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["act", "--canonical", "main#build", "--action", "click"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["act", "--canonical", "main#", "--action", "click"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["history", "--count", "65"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["find", "--limit", "many"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["find", "--limit", "0"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
match ui_access_cli_parse_request(["snapshot", "--invented"]):
    Err(e): expect(e.code).to_equal("invalid_argument")
    Ok(_): expect(false).to_equal(true)
```

</details>

#### keeps database action fallback read-only and fail-closed

- keeps database action fallback read-only and fail-closed
   - Expected: read_error.code equals `source_unavailable`
   - Expected: act_error.code equals `source_unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps database action fallback read-only and fail-closed")
val read_error = ui_access_cli_db_error("snapshot", "/tmp/ui.db")
expect(read_error.code).to_equal("source_unavailable")
expect(read_error.message).to_contain("unavailable")
val act_error = ui_access_cli_db_error("act", "/tmp/ui.db")
expect(act_error.code).to_equal("source_unavailable")
expect(act_error.message).to_contain("read-only")
```

</details>

#### maps live transport failures to the stable shared taxonomy

- maps live transport failures to the stable shared taxonomy
   - Expected: ui_access_cli_http_error(500, "", "").code equals `source_unavailable`
   - Expected: ui_access_cli_http_error(409, "", "prompt required").code equals `interaction_required`
   - Expected: ui_access_cli_http_error(403, "", "denied").code equals `permission_denied`
   - Expected: ui_access_cli_http_error(409, "", "unsupported").code equals `unsupported_action`
   - Expected: ui_access_cli_http_error(404, "", "missing").code equals `target_not_found`
   - Expected: ui_access_cli_http_error(409, "", "stale").code equals `stale_target`
   - Expected: ui_access_cli_http_error(409, "", "disabled").code equals `target_disabled`
   - Expected: ui_access_cli_http_error(409, "", "busy").code equals `target_busy`
   - Expected: ui_access_cli_http_error(504, "", "").code equals `timeout`
   - Expected: ui_access_cli_http_error(400, "", "bad input").code equals `invalid_argument`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps live transport failures to the stable shared taxonomy")
expect(ui_access_cli_http_error(500, "", "").code).to_equal("source_unavailable")
expect(ui_access_cli_http_error(409, "", "prompt required").code).to_equal("interaction_required")
expect(ui_access_cli_http_error(403, "", "denied").code).to_equal("permission_denied")
expect(ui_access_cli_http_error(409, "", "unsupported").code).to_equal("unsupported_action")
expect(ui_access_cli_http_error(404, "", "missing").code).to_equal("target_not_found")
expect(ui_access_cli_http_error(409, "", "stale").code).to_equal("stale_target")
expect(ui_access_cli_http_error(409, "", "disabled").code).to_equal("target_disabled")
expect(ui_access_cli_http_error(409, "", "busy").code).to_equal("target_busy")
expect(ui_access_cli_http_error(504, "", "").code).to_equal("timeout")
expect(ui_access_cli_http_error(400, "", "bad input").code).to_equal("invalid_argument")
```

</details>

#### keeps post-dispatch timeout correlation and fail-safe guidance

- keeps post-dispatch timeout correlation and fail-safe guidance
   - Expected: error.code equals `timeout`
   - Expected: error.request_id equals `ui-act-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps post-dispatch timeout correlation and fail-safe guidance")
val error = ui_access_post_dispatch_error(ui_access_cli_http_error(504, "", ""), "ui-act-7")
expect(error.code).to_equal("timeout")
expect(error.request_id).to_equal("ui-act-7")
expect(error.hint).to_contain("Action may have dispatched; inspect history")
```

</details>

#### decodes live list snapshots through the common projector

- decodes live list snapshots through the common projector
   - Expected: access_render_json(live) equals `access_render_json(expected)`
   - Expected: live.rows[1][0] equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes live list snapshots through the common projector")
val snapshot = _ui_access_list_snapshot()
val live = ui_access_window_result_from_snapshot_json(ui_access_snapshot_to_json(snapshot))?
val expected = access_result_from_snapshot(ACCESS_OPERATION_LIST, "simple_ui", "", snapshot, 1000)
expect(access_render_json(live)).to_equal(access_render_json(expected))
expect(live.rows[1][0]).to_equal("a")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/access_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple ui access CLI adapter.
- simple ui access CLI adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f90d385bddf95eaa34f753b28c2f9b8a413b0b3d714655e8d35ae0cf7b66842`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f90d385bddf95eaa34f753b28c2f9b8a413b0b3d714655e8d35ae0cf7b66842`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f90d385bddf95eaa34f753b28c2f9b8a413b0b3d714655e8d35ae0cf7b66842`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/ui/access_cli_spec.spl
mirror: doc/06_spec/01_unit/app/ui/access_cli_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/access_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/access_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/access_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/access_cli_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes UI backends to the deployed compiled sibling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/access_cli_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the six T32-style operations through shared descriptors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/access_cli_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps reads to the existing UI test API with encoded selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
