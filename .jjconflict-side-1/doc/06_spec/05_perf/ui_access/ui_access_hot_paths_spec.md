# Ui Access Hot Paths Specification

> <details>

<!-- sdn-diagram:id=ui_access_hot_paths_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_hot_paths_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_hot_paths_spec -> std
ui_access_hot_paths_spec -> common
ui_access_hot_paths_spec -> nogc_sync_mut
ui_access_hot_paths_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_hot_paths_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. var session =  session fixture
2. session dispatch
3. session current state
   - Expected: preflight.0 equals `200`
4.  check budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session =  session fixture
2. session dispatch
3. session current state
   - Expected: preflight.0 equals `200`
4.  check budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session =  session fixture
2. session dispatch
3. session current state
   - Expected: seed.0 equals `200`
4.  check budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
