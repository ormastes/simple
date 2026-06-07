# session_store_spec

> Validates the file-backed session store that persists PlaySession records across short-lived CLI processes.

<!-- sdn-diagram:id=session_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_store_spec -> std
session_store_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# session_store_spec

Validates the file-backed session store that persists PlaySession records across short-lived CLI processes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PLAY-005 |
| Category | App \| Play |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/play/session_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Validates the file-backed session store that persists PlaySession
records across short-lived CLI processes.

## Scenarios

### session_store_init

#### creates the store directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = session_store_init()
expect(result).to_equal(true)
```

</details>

### session_store save and load

#### round-trips a session

1. session store init
2. session store save
   - Expected: s.id equals `test-session-1234`
   - Expected: s.backend equals `cdp`
   - Expected: s.state equals `ready`
   - Expected: s.pid equals `42`
   - Expected: s.ws_url equals `ws://127.0.0.1:9222/devtools/browser/abc`
   - Expected: s.first_window_id equals `target-123`
   - Expected: s.artifacts_dir equals `doc/08_tracking/test/play/test-session-1234`
   - Expected: s.args.length() equals `2`
   - Expected: s.args[0] equals `.`
   - Expected: s.args[1] equals `--no-sandbox`
3. fail
4. session store delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
session_store_init()
val sess = _test_session()
session_store_save(sess)
val loaded = session_store_load("test-session-1234")
match loaded:
    case Some(s):
        expect(s.id).to_equal("test-session-1234")
        expect(s.backend).to_equal("cdp")
        expect(s.state).to_equal("ready")
        expect(s.pid).to_equal(42)
        expect(s.ws_url).to_equal("ws://127.0.0.1:9222/devtools/browser/abc")
        expect(s.first_window_id).to_equal("target-123")
        expect(s.artifacts_dir).to_equal("doc/08_tracking/test/play/test-session-1234")
        expect(s.args.length()).to_equal(2)
        expect(s.args[0]).to_equal(".")
        expect(s.args[1]).to_equal("--no-sandbox")
    case nil:
        fail("session_store_load did not return saved session")
# Clean up
session_store_delete("test-session-1234")
```

</details>

#### returns nil for non-existent session

1. session store init
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
session_store_init()
val loaded = session_store_load("does-not-exist-xyz")
match loaded:
    case Some(_):
        fail("session_store_load returned a session for a missing id")
    case nil:
        expect(loaded).to_be_nil()
```

</details>

### session_store delete

#### removes a saved session

1. session store init
2. session store save
   - Expected: del is true
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
session_store_init()
val sess = _test_session()
session_store_save(sess)
val del = session_store_delete("test-session-1234")
expect(del).to_equal(true)
val loaded = session_store_load("test-session-1234")
match loaded:
    case Some(_):
        fail("session_store_delete left the deleted session loadable")
    case nil:
        expect(loaded).to_be_nil()
```

</details>

#### returns true for already-deleted session

1. session store init
   - Expected: del is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
session_store_init()
val del = session_store_delete("never-existed-99")
expect(del).to_equal(true)
```

</details>

### session_store list

#### lists saved sessions

1. session store init
2. session store save
   - Expected: found is true
3. session store delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
session_store_init()
val sess = _test_session()
session_store_save(sess)
val all = session_store_list()
var found = false
for s in all:
    if s.id == "test-session-1234":
        found = true
expect(found).to_equal(true)
# Clean up
session_store_delete("test-session-1234")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
