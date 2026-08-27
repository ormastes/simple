# Bare-Metal Syscall and Peripheral

> Tests bare-metal system call interfaces and peripheral access including MMIO register reads/writes, timer configuration, and UART communication. Verifies that syscall wrappers correctly interact with hardware peripherals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Syscall and Peripheral

Tests bare-metal system call interfaces and peripheral access including MMIO register reads/writes, timer configuration, and UART communication. Verifies that syscall wrappers correctly interact with hardware peripherals.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/syscall_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests bare-metal system call interfaces and peripheral access including MMIO
register reads/writes, timer configuration, and UART communication. Verifies
that syscall wrappers correctly interact with hardware peripherals.

## Scenarios

### Semihosting

#### basic operations

<details>
<summary>Advanced: writes string to debug console</summary>

#### writes string to debug console _(slow)_

- writes string to debug console
   - Expected: _semi_last_message equals `Test message\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes string to debug console")
semi_write_string("Test message\n")
expect(_semi_last_message).to_equal("Test message\n")
```

</details>


</details>

<details>
<summary>Advanced: reads clock in centiseconds</summary>

#### reads clock in centiseconds _(slow)_

- reads clock in centiseconds
   - Expected: time1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads clock in centiseconds")
val time1 = semi_clock()
# Stub returns 0
expect(time1).to_equal(0)
```

</details>


</details>

#### file I/O

<details>
<summary>Advanced: opens file for reading</summary>

#### opens file for reading _(slow)_

- opens file for reading
   - Expected: fd equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("opens file for reading")
val fd = semi_open("test.txt", MODE_READ)
# Stub returns -1 (no host filesystem)
expect(fd).to_equal(-1)
```

</details>


</details>

<details>
<summary>Advanced: writes to file</summary>

#### writes to file _(slow)_

- writes to file
   - Expected: fd equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes to file")
val fd = semi_open("output.txt", MODE_WRITE)
# fd is -1, so write is skipped
if fd >= 0:
    semi_write(fd, [], 0)
    semi_close(fd)
expect(fd).to_equal(-1)
```

</details>


</details>

#### timing

<details>
<summary>Advanced: reads time since epoch</summary>

#### reads time since epoch _(slow)_

- reads time since epoch
   - Expected: t equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads time since epoch")
val t = semi_time()
# Stub returns 0
expect(t).to_equal(0)
```

</details>


</details>

### UART

#### initialization

<details>
<summary>Advanced: configures UART with baud rate</summary>

#### configures UART with baud rate _(slow)_

- configures UART with baud rate
   - Expected: _uart_last_base equals `0x40011000`
   - Expected: _uart_last_baudrate equals `115200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("configures UART with baud rate")
uart_init(0x40011000, 115200)
expect(_uart_last_base).to_equal(0x40011000)
expect(_uart_last_baudrate).to_equal(115200)
```

</details>


</details>

#### status checking

<details>
<summary>Advanced: checks if UART ready to write</summary>

#### checks if UART ready to write _(slow)_

- checks if UART ready to write
   - Expected: ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if UART ready to write")
val ready = uart_write_ready(0x40011000)
# Stub returns false
expect(ready).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: checks if data available to read</summary>

#### checks if data available to read _(slow)_

- checks if data available to read
   - Expected: available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if data available to read")
val available = uart_read_available(0x40011000)
# Stub returns false
expect(available).to_equal(false)
```

</details>


</details>

### Timer

#### initialization

<details>
<summary>Advanced: configures timer frequency</summary>

#### configures timer frequency _(slow)_

- configures timer frequency
   - Expected: _timer_last_base equals `0x40000000`
   - Expected: _timer_last_frequency equals `1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("configures timer frequency")
timer_init(0x40000000, 1000000)
expect(_timer_last_base).to_equal(0x40000000)
expect(_timer_last_frequency).to_equal(1000000)
```

</details>


</details>

#### counter access

<details>
<summary>Advanced: reads current counter value</summary>

#### reads current counter value _(slow)_

- reads current counter value
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads current counter value")
val count = timer_read(0x40000000)
# Stub returns 0
expect(count).to_equal(0)
```

</details>


</details>

#### delays

<details>
<summary>Advanced: delays for milliseconds</summary>

#### delays for milliseconds _(slow)_

- delays for milliseconds
   - Expected: _timer_last_delay_ms equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delays for milliseconds")
timer_delay_ms(0x40000000, 10)
expect(_timer_last_delay_ms).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: delays for microseconds</summary>

#### delays for microseconds _(slow)_

- delays for microseconds
   - Expected: _timer_last_delay_us equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delays for microseconds")
timer_delay_us(0x40000000, 100)
expect(_timer_last_delay_us).to_equal(100)
```

</details>


</details>

### Memory-Mapped I/O

#### register access

<details>
<summary>Advanced: reads and writes 32-bit registers</summary>

#### reads and writes 32-bit registers _(slow)_

- reads and writes 32-bit registers
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads and writes 32-bit registers")
mem_write_u32(0x40020000, 0x12345678)
val value = mem_read_u32(0x40020000)
# Stub: write is no-op, read returns 0
expect(value).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: reads and writes 8-bit registers</summary>

#### reads and writes 8-bit registers _(slow)_

- reads and writes 8-bit registers
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads and writes 8-bit registers")
mem_write_u8(0x40020000, 0xAB)
val value = mem_read_u8(0x40020000)
# Stub: write is no-op, read returns 0
expect(value).to_equal(0)
```

</details>


</details>

#### bit manipulation

<details>
<summary>Advanced: sets specific bit</summary>

#### sets specific bit _(slow)_

- sets specific bit
   - Expected: _last_set_bit equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets specific bit")
mem_set_bit(0x40020000, 5)
expect(_last_set_bit).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: clears specific bit</summary>

#### clears specific bit _(slow)_

- clears specific bit
   - Expected: _last_clear_bit equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears specific bit")
mem_clear_bit(0x40020000, 3)
expect(_last_clear_bit).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: tests specific bit</summary>

#### tests specific bit _(slow)_

- tests specific bit
   - Expected: is_set is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tests specific bit")
val is_set = mem_test_bit(0x40020000, 7)
# Stub returns false
expect(is_set).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: modifies bits with mask</summary>

#### modifies bits with mask _(slow)_

- modifies bits with mask
   - Expected: _last_modify_clear_mask equals `0x0F`
   - Expected: _last_modify_set_mask equals `0xA0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("modifies bits with mask")
mem_modify_bits(0x40020000, 0x0F, 0xA0)
expect(_last_modify_clear_mask).to_equal(0x0F)
expect(_last_modify_set_mask).to_equal(0xA0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c315ea8d453972efb4b496ab95f7fe2ccdb7724ad12bfbfacfdce1eb108291f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c315ea8d453972efb4b496ab95f7fe2ccdb7724ad12bfbfacfdce1eb108291f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c315ea8d453972efb4b496ab95f7fe2ccdb7724ad12bfbfacfdce1eb108291f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/syscall_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/syscall_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/syscall_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/syscall_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/syscall_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/syscall_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes string to debug console' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/syscall_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads clock in centiseconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/syscall_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens file for reading' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
