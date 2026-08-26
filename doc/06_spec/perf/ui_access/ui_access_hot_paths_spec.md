# Ui Access Hot Paths Specification

> Tests covering ui_access hot paths perf smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Hot Paths Specification

## Scenarios

### ui_access hot paths perf smoke

<details>
<summary>Advanced: snapshot route stays interactive on a multi-surface in-memory session</summary>

#### snapshot route stays interactive on a multi-surface in-memory session _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual UI access hot-path evidence (expected show, folded, detail, or skip)


- drive 100 snapshot requests against a 3-surface session and time them
   - Expected: preflight.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-UI-ACCESS-HOTPATHS
step("drive 100 snapshot requests against a 3-surface session and time them")
var session = _session_fixture()
val inject_event = \event:
    session.dispatch(event)

val snapshot_request = \:
    handle_test_request(
        "/api/test/ui/snapshot",
        "GET",
        "",
        session.current_state(),
        inject_event,
        session
    )
val preflight = snapshot_request()
# oracle: 200 = successful route response before timing begins.
expect(preflight.0).to_equal(200)
expect(preflight.2).to_contain("\"popup\"")

val elapsed = _bench_request("ui_access snapshot route", 5, 100, snapshot_request)
_check_budget("ui_access snapshot route", elapsed, 100, 2000)
```

</details>


</details>

<details>
<summary>Advanced: query route stays interactive across kind/text filters</summary>

#### query route stays interactive across kind/text filters _(slow)_

- run filtered button queries on the popup surface and time them
   - Expected: preflight.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-UI-ACCESS-HOTPATHS
step("run filtered button queries on the popup surface and time them")
var session = _session_fixture()
val inject_event = \event:
    session.dispatch(event)

val query_request = \:
    handle_test_request(
        "/api/test/ui/query?surface_id=popup&kind=button&text=Go&focused_only=false&limit=16",
        "GET",
        "",
        session.current_state(),
        inject_event,
        session
    )
val preflight = query_request()
# oracle: 200 = successful route response before timing begins.
expect(preflight.0).to_equal(200)
expect(preflight.2).to_contain("\"match_count\"")
# oracle: popup#popup_button_0 is the first Go button of the popup fixture.
expect(preflight.2).to_contain("popup#popup_button_0")

val elapsed = _bench_request("ui_access query route", 5, 100, query_request)
_check_budget("ui_access query route", elapsed, 100, 2000)
```

</details>


</details>

<details>
<summary>Advanced: ensure-style state loop stays interactive on a canonical button</summary>

#### ensure-style state loop stays interactive on a canonical button _(slow)_

- drive state-ensure POSTs on main#main_button_0 and time them
   - Expected: seed.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-UI-ACCESS-HOTPATHS
step("drive state-ensure POSTs on main#main_button_0 and time them")
var session = _session_fixture()
val inject_event = \event:
    session.dispatch(event)

val ensure_body = "{\"surface_id\":\"main\",\"canonical_id\":\"main#main_button_0\",\"state_key\":\"selected\",\"state_value\":\"true\"}"
val ensure_request = \:
    handle_test_request(
        "/api/test/ui/state",
        "POST",
        ensure_body,
        session.current_state(),
        inject_event,
        session
    )

val seed = ensure_request()
# oracle: 200 = successful route response before timing begins.
expect(seed.0).to_equal(200)
expect(seed.2).to_contain("\"state_key\":\"selected\"")

val elapsed = _bench_request("ui_access ensure-style state route", 5, 100, ensure_request)
_check_budget("ui_access ensure-style state route", elapsed, 100, 2000)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/ui_access/ui_access_hot_paths_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_access hot paths perf smoke.
- ui_access hot paths perf smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-UI-ACCESS-HOTPATHS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d076913df0de8327f04d1297d6c2ad2eb3915fb6c6362e864b97dc6627d967a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d076913df0de8327f04d1297d6c2ad2eb3915fb6c6362e864b97dc6627d967a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d076913df0de8327f04d1297d6c2ad2eb3915fb6c6362e864b97dc6627d967a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/perf/ui_access/ui_access_hot_paths_spec.spl
mirror: doc/06_spec/perf/ui_access/ui_access_hot_paths_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/ui_access/ui_access_hot_paths_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/ui_access/ui_access_hot_paths_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/ui_access/ui_access_hot_paths_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/ui_access/ui_access_hot_paths_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/ui_access/ui_access_hot_paths_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshot route stays interactive on a multi-surface in-memory session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/ui_access/ui_access_hot_paths_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'query route stays interactive across kind/text filters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/ui_access/ui_access_hot_paths_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ensure-style state loop stays interactive on a canonical button' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
