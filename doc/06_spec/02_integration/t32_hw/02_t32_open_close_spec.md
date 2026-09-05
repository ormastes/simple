# 02 T32 Open Close Specification

> 1. Ok

<!-- sdn-diagram:id=02_t32_open_close_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=02_t32_open_close_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

02_t32_open_close_spec -> std
02_t32_open_close_spec -> app
02_t32_open_close_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=02_t32_open_close_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 02 T32 Open Close Specification

## Scenarios

### T32 hardware session open/close

#### successful connection

#### opens T32 session

1. Ok
   - Expected: client.connected is true
2. client disconnect
3. Err
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_connect()
match result:
    Ok(client):
        expect(client.connected).to_equal(true)
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### session responds to ping

1. Ok
2. client disconnect
3. Err
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_connect()
match result:
    Ok(client):
        val ping = t32_hw_run_cmd(client, "PING")
        match ping:
            Ok(_): expect("ping ok").to_contain("ok")
            Err(e): expect("ping failed: {e}").to_equal("ok")
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### evaluates VERSION.BUILD()

1. Ok
2. client disconnect
3. Err
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_connect()
match result:
    Ok(client):
        val ver = t32_hw_eval(client, "VERSION.BUILD()")
        match ver:
            Ok(v): expect(v.len()).to_be_greater_than(0)
            Err(e): expect("eval failed: {e}").to_equal("ok")
        client.disconnect()
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### session teardown

#### closes session cleanly

1. Ok
2. client disconnect
   - Expected: client.connected is false
3. Err
   - Expected: "connect failed: {e}" equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_connect()
match result:
    Ok(client):
        client.disconnect()
        expect(client.connected).to_equal(false)
    Err(e):
        expect("connect failed: {e}").to_equal("connected")
```

</details>

#### negative cases

#### connection fails on bad port

1. host: t32 hw host


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = DebugConfig(
    host: t32_hw_host(),
    port: 19999,
    program: "",
    args: [],
    debugger: "t32",
    remote: true
)
val result = Trace32Client.connect(config)
match result:
    Ok(_): expect("should not connect").to_equal("error")
    Err(_): expect("bad port rejected").to_contain("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/02_t32_open_close_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 hardware session open/close

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
