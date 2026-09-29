# Stlink Tools Specification

> Tests covering StLinkToolsClient STM32H7 probe, StLinkToolsClient STM32WB probe, StLinkToolsClient flash operations, StLinkToolsClient disconnect.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stlink Tools Specification

## Scenarios

### StLinkToolsClient STM32H7 probe

#### probe info returns correct serial

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe info returns correct serial
   - Expected: info != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe info returns correct serial")
val client = MockStLinkClient.for_stm32h7()
val info = client.probe_info()
expect(info != nil).to_equal(true)
```

</details>

#### chip_id returns 0x480 for STM32H7

- chip_id returns 0x480 for STM32H7
   - Expected: chip != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chip_id returns 0x480 for STM32H7")
val client = MockStLinkClient.for_stm32h7()
val chip = client.chip_id()
expect(chip != nil).to_equal(true)
```

</details>

#### flash_size returns 2MB for STM32H7

- flash_size returns 2MB for STM32H7
   - Expected: size != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash_size returns 2MB for STM32H7")
val client = MockStLinkClient.for_stm32h7()
val size = client.flash_size()
expect(size != nil).to_equal(true)
```

</details>

#### sram_size returns 128KB for STM32H7

- sram_size returns 128KB for STM32H7
   - Expected: size != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sram_size returns 128KB for STM32H7")
val client = MockStLinkClient.for_stm32h7()
val size = client.sram_size()
expect(size != nil).to_equal(true)
```

</details>

#### serial is correct

- serial is correct
   - Expected: client.serial equals `002600213137510833333639`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serial is correct")
val client = MockStLinkClient.for_stm32h7()
expect(client.serial).to_equal("002600213137510833333639")
```

</details>

### StLinkToolsClient STM32WB probe

#### chip_id returns 0x495 for STM32WB

- chip_id returns 0x495 for STM32WB
   - Expected: chip != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chip_id returns 0x495 for STM32WB")
val client = MockStLinkClient.for_stm32wb()
val chip = client.chip_id()
expect(chip != nil).to_equal(true)
```

</details>

#### flash_size returns 1MB for STM32WB

- flash_size returns 1MB for STM32WB
   - Expected: size != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash_size returns 1MB for STM32WB")
val client = MockStLinkClient.for_stm32wb()
val size = client.flash_size()
expect(size != nil).to_equal(true)
```

</details>

#### sram_size returns 256KB for STM32WB

- sram_size returns 256KB for STM32WB
   - Expected: size != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sram_size returns 256KB for STM32WB")
val client = MockStLinkClient.for_stm32wb()
val size = client.sram_size()
expect(size != nil).to_equal(true)
```

</details>

#### serial is correct

- serial is correct
   - Expected: client.serial equals `0671FF555755846687041216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serial is correct")
val client = MockStLinkClient.for_stm32wb()
expect(client.serial).to_equal("0671FF555755846687041216")
```

</details>

### StLinkToolsClient flash operations

#### flash_write sets last command

- flash_write sets last command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash_write sets last command")
var client = MockStLinkClient.for_stm32h7()
client.flash_write("app.bin", 0x08000000)
expect(client.last_command).to_contain("st-flash write")
```

</details>

#### flash_erase sets last command

- flash_erase sets last command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash_erase sets last command")
var client = MockStLinkClient.for_stm32h7()
client.flash_erase()
expect(client.last_command).to_contain("st-flash erase")
```

</details>

#### reset sets last command

- reset sets last command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset sets last command")
var client = MockStLinkClient.for_stm32h7()
client.reset()
expect(client.last_command).to_contain("st-flash reset")
```

</details>

#### read_memory returns data

- read_memory returns data
   - Expected: mem != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_memory returns data")
val client = MockStLinkClient.for_stm32h7()
val mem = client.read_memory(0x08000000, 4)
expect(mem != nil).to_equal(true)
```

</details>

### StLinkToolsClient disconnect

#### disconnect sets connected to false

- disconnect sets connected to false
   - Expected: client.connected is true
   - Expected: client.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disconnect sets connected to false")
var client = MockStLinkClient.for_stm32h7()
expect(client.connected).to_equal(true)
client.disconnect()
expect(client.connected).to_equal(false)
```

</details>

#### operations after disconnect fail

- operations after disconnect fail
   - Expected: client.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("operations after disconnect fail")
var client = MockStLinkClient.for_stm32h7()
client.disconnect()
val result = client.chip_id()
expect(client.connected).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/stlink_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StLinkToolsClient STM32H7 probe, StLinkToolsClient STM32WB probe, StLinkToolsClient flash operations, StLinkToolsClient disconnect.
- StLinkToolsClient STM32H7 probe
- StLinkToolsClient STM32WB probe
- StLinkToolsClient flash operations
- StLinkToolsClient disconnect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f4615e55320294cf1ea01c4d090f0b28a4f0b32d619774c1b3de8983b97b456`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f4615e55320294cf1ea01c4d090f0b28a4f0b32d619774c1b3de8983b97b456`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f4615e55320294cf1ea01c4d090f0b28a4f0b32d619774c1b3de8983b97b456`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/debug/remote/stlink_tools_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/stlink_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/stlink_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/stlink_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/stlink_tools_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe info returns correct serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stlink_tools_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chip_id returns 0x480 for STM32H7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/stlink_tools_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flash_size returns 2MB for STM32H7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
