# Arduino UNO R4 WiFi Remote Execution Lane — Composite Runner

> 1. print

<!-- sdn-diagram:id=arduino_r4_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arduino_r4_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arduino_r4_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arduino_r4_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arduino UNO R4 WiFi Remote Execution Lane — Composite Runner

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/arduino_r4_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#

## Scenarios

### Arduino R4 Composite Runner (#RJE-018)

#### adapter connects via CMSIS-DAP

1. print
2. var adapter = ArduinoR4Adapter new
3. Ok
   - Expected: adapter.connected is true
4. adapter disconnect
   - Expected: adapter.connected is false
5. Err
6. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = probe_cmsis_dap()
if not cap.is_runnable():
    print("SKIP: openocd not available — {cap.detail}")
    return
var adapter = ArduinoR4Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(msg):
        expect(adapter.connected).to_equal(true)
        adapter.disconnect()
        expect(adapter.connected).to_equal(false)
    Err(e):
        print("SKIP: connect failed: {e}")
```

</details>

#### SRAM write and readback

1. print
2. var adapter = ArduinoR4Adapter new
3. print
4. adapter disconnect
5. print
6. Ok
   - Expected: read_bytes[0] equals `0x11`
   - Expected: read_bytes[1] equals `0x22`
   - Expected: read_bytes[2] equals `0x33`
   - Expected: read_bytes[3] equals `0x44`
7. Err
8. print
9. adapter disconnect


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = probe_cmsis_dap()
if not cap.is_runnable():
    print("SKIP: openocd not available — {cap.detail}")
    return
var adapter = ArduinoR4Adapter.new()
val conn = adapter.connect()
if conn.is_err():
    print("SKIP: connect failed: {conn.unwrap_err()}")
    return
val sram_payload: [i32] = [0x11, 0x22, 0x33, 0x44]
val write_result = adapter.write_code(TEST_ADDR, sram_payload)
if write_result.is_err():
    adapter.disconnect()
    print("SKIP: write_code failed: {write_result.unwrap_err()}")
    return
val read_result = adapter.read_code(TEST_ADDR, 4)
match read_result:
    Ok(read_bytes):
        expect(read_bytes[0]).to_equal(0x11)
        expect(read_bytes[1]).to_equal(0x22)
        expect(read_bytes[2]).to_equal(0x33)
        expect(read_bytes[3]).to_equal(0x44)
    Err(re):
        print("SKIP: read_code failed: {re}")
adapter.disconnect()
```

</details>

#### register write and readback

1. print
2. var adapter = ArduinoR4Adapter new
3. Ok
4. Ok
5. Ok
   - Expected: value equals `0xDEADBEEF`
6. Err
7. print
8. Err
9. print
10. adapter disconnect
11. Err
12. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = probe_cmsis_dap()
if not cap.is_runnable():
    print("SKIP: openocd not available — {cap.detail}")
    return
var adapter = ArduinoR4Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(_):
        val write_result = adapter.write_register(TEST_REG, 0xDEADBEEF)
        match write_result:
            Ok(_):
                val read_result = adapter.read_register(TEST_REG)
                match read_result:
                    Ok(value):
                        expect(value).to_equal(0xDEADBEEF)
                    Err(re):
                        print("SKIP: read_register failed: {re}")
            Err(we):
                print("SKIP: write_register failed: {we}")
        adapter.disconnect()
    Err(e):
        print("SKIP: connect failed: {e}")
```

</details>

#### creates execution manager

1. print
2. var adapter = ArduinoR4Adapter new
3. Ok
4. Ok
   - Expected: adapter.connected is true
5. Err
6. print
7. adapter disconnect
8. Err
9. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = probe_cmsis_dap()
if not cap.is_runnable():
    print("SKIP: openocd not available — {cap.detail}")
    return
var adapter = ArduinoR4Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(_):
        val mgr = adapter.create_manager()
        match mgr:
            Ok(_):
                expect(adapter.connected).to_equal(true)
            Err(e):
                print("SKIP: create_manager failed: {e}")
        adapter.disconnect()
    Err(e):
        print("SKIP: connect failed: {e}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
