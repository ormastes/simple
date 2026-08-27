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
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- snapshot route stays interactive on a multi-surface in-memory session
   - Expected: preflight.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("snapshot route stays interactive on a multi-surface in-memory session")
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

- query route stays interactive across kind/text filters
   - Expected: preflight.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("query route stays interactive across kind/text filters")
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
expect(preflight.0).to_equal(200)
expect(preflight.2).to_contain("\"match_count\"")
expect(preflight.2).to_contain("popup#popup_button_0")

val elapsed = _bench_request("ui_access query route", 5, 100, query_request)
_check_budget("ui_access query route", elapsed, 100, 2000)
```

</details>


</details>

<details>
<summary>Advanced: ensure-style state loop stays interactive on a canonical button</summary>

#### ensure-style state loop stays interactive on a canonical button _(slow)_

- ensure-style state loop stays interactive on a canonical button
   - Expected: seed.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("ensure-style state loop stays interactive on a canonical button")
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
| Category | Other |
| Status | Active |
| Source | `test/05_perf/ui_access/ui_access_hot_paths_spec.spl` |
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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `757995f48541c53a8623c56b00e930c1ea89d5db084da59cf479ac13086910a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `757995f48541c53a8623c56b00e930c1ea89d5db084da59cf479ac13086910a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `757995f48541c53a8623c56b00e930c1ea89d5db084da59cf479ac13086910a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/ui_access/ui_access_hot_paths_spec.spl
mirror: doc/06_spec/05_perf/ui_access/ui_access_hot_paths_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/ui_access/ui_access_hot_paths_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/ui_access/ui_access_hot_paths_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/ui_access/ui_access_hot_paths_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/ui_access/ui_access_hot_paths_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshot route stays interactive on a multi-surface in-memory session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/ui_access/ui_access_hot_paths_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'query route stays interactive across kind/text filters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/ui_access/ui_access_hot_paths_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ensure-style state loop stays interactive on a canonical button' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
