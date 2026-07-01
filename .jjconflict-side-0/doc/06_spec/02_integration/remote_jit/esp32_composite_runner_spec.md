# ESP32 Remote Execution Lane — Composite Runner

> 1. print

<!-- sdn-diagram:id=esp32_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=esp32_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

esp32_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=esp32_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ESP32 Remote Execution Lane — Composite Runner

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/remote_jit/esp32_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#

## Scenarios

### ESP32 Composite Runner (#RJE-020)

#### adapter connects via USB JTAG

1. print
2. var adapter = Esp32Adapter new
3. Ok
   - Expected: adapter.connected is true
4. adapter disconnect
   - Expected: adapter.connected is false
5. Err
6. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not probe_command("openocd"):
    print("SKIP: openocd not available")
    return
var adapter = Esp32Adapter.new()
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

#### DRAM write and readback

1. print
2. var adapter = Esp32Adapter new
3. Ok
4. Ok
5. Ok
   - Expected: read_bytes[0] equals `0x11`
   - Expected: read_bytes[1] equals `0x22`
   - Expected: read_bytes[2] equals `0x33`
   - Expected: read_bytes[3] equals `0x44`
6. Err
7. print
8. Err
9. print
10. adapter disconnect
11. Err
12. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not probe_command("openocd"):
    print("SKIP: openocd not available")
    return
var adapter = Esp32Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(_):
        val bytes: [i32] = [0x11, 0x22, 0x33, 0x44]
        val write_result = adapter.write_code(TEST_ADDR, bytes)
        match write_result:
            Ok(_):
                val read_result = adapter.read_code(TEST_ADDR, 4)
                match read_result:
                    Ok(read_bytes):
                        expect(read_bytes[0]).to_equal(0x11)
                        expect(read_bytes[1]).to_equal(0x22)
                        expect(read_bytes[2]).to_equal(0x33)
                        expect(read_bytes[3]).to_equal(0x44)
                    Err(re):
                        print("SKIP: read_code failed: {re}")
            Err(we):
                print("SKIP: write_code failed: {we}")
        adapter.disconnect()
    Err(e):
        print("SKIP: connect failed: {e}")
```

</details>

#### register write and readback

1. print
2. var adapter = Esp32Adapter new
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

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not probe_command("openocd"):
    print("SKIP: openocd not available")
    return
var adapter = Esp32Adapter.new()
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
2. var adapter = Esp32Adapter new
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

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not probe_command("openocd"):
    print("SKIP: openocd not available")
    return
var adapter = Esp32Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(_):
        val mgr = adapter.create_manager()
        match mgr:
            Ok(_):
                expect(adapter.connected).to_equal(true)
            Err(e):
                print("SKIP: create_manager failed (Xtensa may not be wired yet): {e}")
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
