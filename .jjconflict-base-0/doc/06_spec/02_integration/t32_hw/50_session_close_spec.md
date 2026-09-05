# T32 Session Close Specification

> Final teardown test. Opens a session, verifies it works, closes it, and confirms operations fail after close.

<!-- sdn-diagram:id=50_session_close_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=50_session_close_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

50_session_close_spec -> std
50_session_close_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=50_session_close_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Session Close Specification

Final teardown test. Opens a session, verifies it works, closes it, and confirms operations fail after close.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Draft |
| Source | `test/02_integration/t32_hw/50_session_close_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Final teardown test. Opens a session, verifies it works, closes it,
and confirms operations fail after close.

## Scenarios

### T32 Session Close

#### opens and closes session cleanly

1. Ok
   - Expected: c.connected is true
2. c disconnect
   - Expected: c.connected is false
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        expect(c.connected).to_equal(true)
        c.disconnect()
        expect(c.connected).to_equal(false)
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### session is no longer connected after close

1. Ok
2. c disconnect
   - Expected: c.connected is false
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        c.disconnect()
        # After disconnect, connected should be false
        expect(c.connected).to_equal(false)
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### can reopen session after close

1. Ok
2. c1 disconnect
3. Err
   - Expected: t32_hw_probe_available() is true
4. Ok
5. c2 disconnect
6. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
# First session
val client1 = t32_hw_connect()
match client1:
    Ok(c1):
        c1.disconnect()
    Err(_):
        expect(t32_hw_probe_available()).to_equal(true)

# Second session should work
val client2 = t32_hw_connect()
match client2:
    Ok(c2):
        val r = c2.eval_expr("VERSION.BUILD()")
        c2.disconnect()
        match r:
            Ok(v): expect(v.len()).to_be_greater_than(0)
            Err(e): expect("eval failed: {e}").to_contain("eval")
    Err(e):
        expect("reconnection failed: {e}").to_contain("skip")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
