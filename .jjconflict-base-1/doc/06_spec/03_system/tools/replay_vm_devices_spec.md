# Replay Vm Devices Specification

> 1. var timer = VirtualTimer create

<!-- sdn-diagram:id=replay_vm_devices_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_vm_devices_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_vm_devices_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_vm_devices_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Vm Devices Specification

## Scenarios

### VirtualTimer create

#### counter is zero after create

1. var timer = VirtualTimer create
   - Expected: timer.counter equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
expect(timer.counter).to_equal(0)
```

</details>

#### irq matches constructor arg

1. var timer = VirtualTimer create
   - Expected: timer.irq equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
expect(timer.irq).to_equal(7)
```

</details>

#### enabled is false after create

1. var timer = VirtualTimer create
   - Expected: timer.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
expect(timer.enabled).to_equal(false)
```

</details>

#### no pending irq after create

1. var timer = VirtualTimer create
   - Expected: timer.pending_irq() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
expect(timer.pending_irq()).to_equal(-1)
```

</details>

### VirtualTimer tick increments counter

#### counter equals tick cycles when enabled

1. var timer = VirtualTimer create
2. timer mmio write
3. timer tick
   - Expected: timer.counter equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
# Enable via mmio_write offset 0x14, value 1
timer.mmio_write(0x14, 1, 4)
timer.tick(100)
expect(timer.counter).to_equal(100)
```

</details>

#### counter stays zero when disabled

1. var timer = VirtualTimer create
2. timer tick
   - Expected: timer.counter equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.tick(100)
expect(timer.counter).to_equal(0)
```

</details>

#### counter accumulates across multiple ticks

1. var timer = VirtualTimer create
2. timer mmio write
3. timer tick
4. timer tick
   - Expected: timer.counter equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)
timer.tick(50)
timer.tick(50)
expect(timer.counter).to_equal(100)
```

</details>

### VirtualTimer interrupt fires at compare

#### no irq before compare_value is reached

1. var timer = VirtualTimer create
2. timer mmio write
3. timer mmio write
4. timer tick
   - Expected: timer.pending_irq() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)    # enable
timer.mmio_write(0x08, 200, 4)  # compare_value = 200
timer.tick(100)
expect(timer.pending_irq()).to_equal(-1)
```

</details>

#### irq fires once compare_value is reached

1. var timer = VirtualTimer create
2. timer mmio write
3. timer mmio write
4. timer tick
   - Expected: irq equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)    # enable
timer.mmio_write(0x08, 100, 4)  # compare_value = 100
timer.tick(100)
val irq = timer.pending_irq()
expect(irq).to_equal(7)
```

</details>

#### irq number matches constructor irq

1. var timer = VirtualTimer create
2. timer mmio write
3. timer mmio write
4. timer tick
   - Expected: timer.pending_irq() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 42)
timer.mmio_write(0x14, 1, 4)
timer.mmio_write(0x08, 10, 4)
timer.tick(10)
expect(timer.pending_irq()).to_equal(42)
```

</details>

#### acknowledge_irq clears pending irq

1. var timer = VirtualTimer create
2. timer mmio write
3. timer mmio write
4. timer tick
5. timer acknowledge irq
   - Expected: timer.pending_irq() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)
timer.mmio_write(0x08, 10, 4)
timer.tick(10)
timer.acknowledge_irq()
expect(timer.pending_irq()).to_equal(-1)
```

</details>

### VirtualTimer snapshot and restore

#### snapshot returns non-empty data

1. var timer = VirtualTimer create
2. timer mmio write
3. timer tick


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)
timer.tick(50)
val data = timer.snapshot()
expect(data.len()).to_be_greater_than(0)
```

</details>

#### snapshot has at least 6 entries

1. var timer = VirtualTimer create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
val data = timer.snapshot()
expect(data.len()).to_be_greater_than(5)
```

</details>

#### counter is restored from snapshot

1. var timer = VirtualTimer create
2. timer mmio write
3. timer tick
4. var timer2 = VirtualTimer create
5. timer2 restore
   - Expected: timer2.counter equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)
timer.tick(77)
val data = timer.snapshot()
# Reset and restore
var timer2 = VirtualTimer.create("timer0", 7)
timer2.restore(data)
expect(timer2.counter).to_equal(77)
```

</details>

#### enabled flag is restored from snapshot

1. var timer = VirtualTimer create
2. timer mmio write
3. var timer2 = VirtualTimer create
4. timer2 restore
   - Expected: timer2.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)  # enable
val data = timer.snapshot()
var timer2 = VirtualTimer.create("timer0", 7)
timer2.restore(data)
expect(timer2.enabled).to_equal(true)
```

</details>

### VirtualSerial create

#### tx_buffer is empty after create

1. var serial = VirtualSerial create
   - Expected: serial.tx_buffer.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
expect(serial.tx_buffer.len()).to_equal(0)
```

</details>

#### rx_buffer is empty after create

1. var serial = VirtualSerial create
   - Expected: serial.rx_buffer.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
expect(serial.rx_buffer.len()).to_equal(0)
```

</details>

#### irq matches constructor arg

1. var serial = VirtualSerial create
   - Expected: serial.irq equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
expect(serial.irq).to_equal(10)
```

</details>

#### no pending irq after create

1. var serial = VirtualSerial create
   - Expected: serial.pending_irq() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
expect(serial.pending_irq()).to_equal(-1)
```

</details>

### VirtualSerial mmio_write TX

#### write byte to offset 0x00 appends to tx_buffer

1. var serial = VirtualSerial create
2. serial mmio write
   - Expected: serial.tx_buffer.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 0x41, 1)
expect(serial.tx_buffer.len()).to_equal(1)
```

</details>

#### written byte value is in tx_buffer

1. var serial = VirtualSerial create
2. serial mmio write
   - Expected: serial.tx_buffer[0] equals `0x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 0x41, 1)
expect(serial.tx_buffer[0]).to_equal(0x41)
```

</details>

#### multiple writes accumulate in tx_buffer

1. var serial = VirtualSerial create
2. serial mmio write
3. serial mmio write
   - Expected: serial.tx_buffer.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 0x41, 1)
serial.mmio_write(0x00, 0x42, 1)
expect(serial.tx_buffer.len()).to_equal(2)
```

</details>

### VirtualSerial mmio_read RX

#### reading offset 0x00 with no input returns 0

1. var serial = VirtualSerial create
   - Expected: byte_val equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
val result = serial.mmio_read(0x00, 1)
val byte_val = match result:
    case Ok(v): v
    case Err(_): -1
expect(byte_val).to_equal(0)
```

</details>

#### inject_input then read returns injected byte

1. var serial = VirtualSerial create
2. serial inject input
   - Expected: byte_val equals `0x48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.inject_input([0x48])
val result = serial.mmio_read(0x00, 1)
val byte_val = match result:
    case Ok(v): v
    case Err(_): -1
expect(byte_val).to_equal(0x48)
```

</details>

#### second inject_input byte readable after first consumed

1. var serial = VirtualSerial create
2. serial inject input
3. serial mmio read
   - Expected: byte_val equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.inject_input([0x41, 0x42])
serial.mmio_read(0x00, 1)
val result = serial.mmio_read(0x00, 1)
val byte_val = match result:
    case Ok(v): v
    case Err(_): -1
expect(byte_val).to_equal(0x42)
```

</details>

### VirtualSerial get_output

#### get_output contains H from byte 72

1. var serial = VirtualSerial create
2. serial mmio write


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 72, 1)   # H
val out = serial.get_output()
expect(out).to_contain("H")
```

</details>

#### get_output contains Hello from bytes 72 101 108 108 111

1. var serial = VirtualSerial create
2. serial mmio write
3. serial mmio write
4. serial mmio write
5. serial mmio write
6. serial mmio write


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 72, 1)   # H
serial.mmio_write(0x00, 101, 1)  # e
serial.mmio_write(0x00, 108, 1)  # l
serial.mmio_write(0x00, 108, 1)  # l
serial.mmio_write(0x00, 111, 1)  # o
val out = serial.get_output()
expect(out).to_contain("Hello")
```

</details>

#### get_output is empty string when nothing written

1. var serial = VirtualSerial create
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var serial = VirtualSerial.create("uart0", 10)
val out = serial.get_output()
expect(out).to_equal("")
```

</details>

### VirtualBlock create

#### sectors.len() equals num_sectors

1. var blk = VirtualBlock create
   - Expected: blk.sectors.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
expect(blk.sectors.len()).to_equal(4)
```

</details>

#### sector_size is 512

1. var blk = VirtualBlock create
   - Expected: blk.sector_size equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
expect(blk.sector_size).to_equal(512)
```

</details>

#### irq matches constructor arg

1. var blk = VirtualBlock create
   - Expected: blk.irq equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
expect(blk.irq).to_equal(5)
```

</details>

### VirtualBlock read empty sector

#### read_sector(0) returns Ok

1. var blk = VirtualBlock create
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val result = blk.read_sector(0)
val is_ok = match result:
    case Ok(_): true
    case Err(_): false
expect(is_ok).to_equal(true)
```

</details>

#### empty sector first byte is zero

1. var blk = VirtualBlock create
   - Expected: first equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val result = blk.read_sector(0)
val first = match result:
    case Ok(data): data[0]
    case Err(_): -1
expect(first).to_equal(0)
```

</details>

#### empty sector has 512 bytes

1. var blk = VirtualBlock create
   - Expected: length equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val result = blk.read_sector(0)
val length = match result:
    case Ok(data): data.len()
    case Err(_): 0
expect(length).to_equal(512)
```

</details>

### VirtualBlock write and read sector

#### written byte appears when sector read back

1. var blk = VirtualBlock create
2. blk write sector
   - Expected: first equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val sec = make_sector_with_first(0xAB)
blk.write_sector(0, sec)
val result = blk.read_sector(0)
val first = match result:
    case Ok(data): data[0]
    case Err(_): -1
expect(first).to_equal(0xAB)
```

</details>

#### write_sector to valid index returns Ok

1. var blk = VirtualBlock create
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val sec = make_sector_zeros()
val result = blk.write_sector(0, sec)
val is_ok = match result:
    case Ok(_): true
    case Err(_): false
expect(is_ok).to_equal(true)
```

</details>

#### sectors are independent after separate writes

1. var blk = VirtualBlock create
2. blk write sector
3. blk write sector
   - Expected: byte0 equals `0xAA`
   - Expected: byte1 equals `0xBB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val sec0 = make_sector_filled(0xAA)
val sec1 = make_sector_filled(0xBB)
blk.write_sector(0, sec0)
blk.write_sector(1, sec1)
val r0 = blk.read_sector(0)
val byte0 = match r0:
    case Ok(data): data[0]
    case Err(_): -1
val r1 = blk.read_sector(1)
val byte1 = match r1:
    case Ok(data): data[0]
    case Err(_): -1
expect(byte0).to_equal(0xAA)
expect(byte1).to_equal(0xBB)
```

</details>

### VirtualBlock out of range

#### read_sector(999) returns Err

1. var blk = VirtualBlock create
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val result = blk.read_sector(999)
val is_err = match result:
    case Ok(_): false
    case Err(_): true
expect(is_err).to_equal(true)
```

</details>

#### write_sector(999) returns Err

1. var blk = VirtualBlock create
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val sec = make_sector_zeros()
val result = blk.write_sector(999, sec)
val is_err = match result:
    case Ok(_): false
    case Err(_): true
expect(is_err).to_equal(true)
```

</details>

#### read_sector(-1) returns Err

1. var blk = VirtualBlock create
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blk = VirtualBlock.create("vblk0", 5, 4)
val result = blk.read_sector(-1)
val is_err = match result:
    case Ok(_): false
    case Err(_): true
expect(is_err).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_vm_devices_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VirtualTimer create
- VirtualTimer tick increments counter
- VirtualTimer interrupt fires at compare
- VirtualTimer snapshot and restore
- VirtualSerial create
- VirtualSerial mmio_write TX
- VirtualSerial mmio_read RX
- VirtualSerial get_output
- VirtualBlock create
- VirtualBlock read empty sector
- VirtualBlock write and read sector
- VirtualBlock out of range

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
