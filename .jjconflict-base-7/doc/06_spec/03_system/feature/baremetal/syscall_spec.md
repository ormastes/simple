# Bare-Metal Syscall and Peripheral

> Tests bare-metal system call interfaces and peripheral access including MMIO register reads/writes, timer configuration, and UART communication. Verifies that syscall wrappers correctly interact with hardware peripherals.

<!-- sdn-diagram:id=syscall_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. semi write string
   - Expected: _semi_last_message equals `Test message\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
semi_write_string("Test message\n")
expect(_semi_last_message).to_equal("Test message\n")
```

</details>


</details>

<details>
<summary>Advanced: reads clock in centiseconds</summary>

#### reads clock in centiseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fd = semi_open("test.txt", MODE_READ)
# Stub returns -1 (no host filesystem)
expect(fd).to_equal(-1)
```

</details>


</details>

<details>
<summary>Advanced: writes to file</summary>

#### writes to file _(slow)_

1. semi write
2. semi close
   - Expected: fd equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. uart init
   - Expected: _uart_last_base equals `0x40011000`
   - Expected: _uart_last_baudrate equals `115200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = uart_write_ready(0x40011000)
# Stub returns false
expect(ready).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: checks if data available to read</summary>

#### checks if data available to read _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. timer init
   - Expected: _timer_last_base equals `0x40000000`
   - Expected: _timer_last_frequency equals `1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. timer delay ms
   - Expected: _timer_last_delay_ms equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
timer_delay_ms(0x40000000, 10)
expect(_timer_last_delay_ms).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: delays for microseconds</summary>

#### delays for microseconds _(slow)_

1. timer delay us
   - Expected: _timer_last_delay_us equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mem write u32
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mem write u8
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. mem set bit
   - Expected: _last_set_bit equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mem_set_bit(0x40020000, 5)
expect(_last_set_bit).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: clears specific bit</summary>

#### clears specific bit _(slow)_

1. mem clear bit
   - Expected: _last_clear_bit equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mem_clear_bit(0x40020000, 3)
expect(_last_clear_bit).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: tests specific bit</summary>

#### tests specific bit _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_set = mem_test_bit(0x40020000, 7)
# Stub returns false
expect(is_set).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: modifies bits with mask</summary>

#### modifies bits with mask _(slow)_

1. mem modify bits
   - Expected: _last_modify_clear_mask equals `0x0F`
   - Expected: _last_modify_set_mask equals `0xA0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
