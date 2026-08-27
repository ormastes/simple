# Arduino UNO R4 WiFi Remote Execution Lane — Composite Runner

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
| Source | `test/integration/remote_jit/arduino_r4_composite_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#

## Scenarios

### Arduino R4 Composite Runner (#RJE-018)

#### adapter connects via CMSIS-DAP

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adapter connects via CMSIS-DAP
   - Expected: adapter.connected is true
   - Expected: adapter.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adapter connects via CMSIS-DAP")
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

- SRAM write and readback
   - Expected: read_bytes[0] equals `0x11`
   - Expected: read_bytes[1] equals `0x22`
   - Expected: read_bytes[2] equals `0x33`
   - Expected: read_bytes[3] equals `0x44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SRAM write and readback")
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

- register write and readback
   - Expected: value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("register write and readback")
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

- creates execution manager
   - Expected: adapter.connected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates execution manager")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad9eba909eebea4be2915c8ed4e9aac894af6f1bccd8b1a77fedd3e143de2531`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad9eba909eebea4be2915c8ed4e9aac894af6f1bccd8b1a77fedd3e143de2531`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad9eba909eebea4be2915c8ed4e9aac894af6f1bccd8b1a77fedd3e143de2531`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/remote_jit/arduino_r4_composite_runner_spec.spl
mirror: doc/06_spec/integration/remote_jit/arduino_r4_composite_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/remote_jit/arduino_r4_composite_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/remote_jit/arduino_r4_composite_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/remote_jit/arduino_r4_composite_runner_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adapter connects via CMSIS-DAP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/arduino_r4_composite_runner_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SRAM write and readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/arduino_r4_composite_runner_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register write and readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
