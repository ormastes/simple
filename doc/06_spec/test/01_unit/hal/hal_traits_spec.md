# HAL Traits Spec

> Unit tests for HAL trait contracts defined in `src/compiler_rust/lib/std/src/bare/hal/`. Covers AC-3 / AC-4 by creating minimal mock implementations of each trait and exercising the public API.

<!-- sdn-diagram:id=hal_traits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_traits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_traits_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_traits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HAL Traits Spec

Unit tests for HAL trait contracts defined in `src/compiler_rust/lib/std/src/bare/hal/`. Covers AC-3 / AC-4 by creating minimal mock implementations of each trait and exercising the public API.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/hal/hal_traits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for HAL trait contracts defined in
`src/compiler_rust/lib/std/src/bare/hal/`. Covers AC-3 / AC-4 by creating
minimal mock implementations of each trait and exercising the public API.

No hardware is required: all tests use in-memory mock structs.

These specs WILL FAIL until Team E lands the mock implementations and wires
up the test stubs. (The traits exist but no mock impls or test file does yet.)

## Scenarios

### AC-3/AC-4 HAL GpioPin trait

#### AC-4: pin() returns the configured pin number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = MockGpioPin(pin_num: 3, port_num: 0, mode: PinMode.Input, state: PinState.Low)
expect(p.pin()).to_equal(3)
```

</details>

#### AC-4: port() returns the configured port number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = MockGpioPin(pin_num: 3, port_num: 1, mode: PinMode.Input, state: PinState.Low)
expect(p.port()).to_equal(1)
```

</details>

#### AC-4: read() returns initial Low state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Input, state: PinState.Low)
expect(p.read() == PinState.Low).to_equal(true)
```

</details>

#### AC-4: write(High) transitions pin to High

1. var p = MockGpioPin
2. p write
   - Expected: p.read() == PinState.High is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.Low)
p.write(PinState.High)
expect(p.read() == PinState.High).to_equal(true)
```

</details>

#### AC-4: toggle() flips Low to High

1. var p = MockGpioPin
2. p toggle
   - Expected: p.is_high() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.Low)
p.toggle()
expect(p.is_high()).to_equal(true)
```

</details>

#### AC-4: toggle() flips High to Low

1. var p = MockGpioPin
2. p toggle
   - Expected: p.is_low() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.High)
p.toggle()
expect(p.is_low()).to_equal(true)
```

</details>

#### AC-4: is_high() returns true when state is High

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.High)
expect(p.is_high()).to_equal(true)
```

</details>

#### AC-4: is_low() returns true when state is Low

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.Low)
expect(p.is_low()).to_equal(true)
```

</details>

#### AC-4: set_high() sets state to High

1. var p = MockGpioPin
2. p set high
   - Expected: p.is_high() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.Low)
p.set_high()
expect(p.is_high()).to_equal(true)
```

</details>

#### AC-4: set_low() sets state to Low

1. var p = MockGpioPin
2. p set low
   - Expected: p.is_low() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = MockGpioPin(pin_num: 0, port_num: 0, mode: PinMode.Output, state: PinState.High)
p.set_low()
expect(p.is_low()).to_equal(true)
```

</details>

### AC-3/AC-4 HAL Uart trait

#### AC-4: write_byte appends byte to buffer

1. var u = MockUart
2. u write byte
   - Expected: u.buf.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
var u = MockUart(buf: buf, head: 0)
u.write_byte(0x41)
expect(u.buf.len()).to_equal(1)
```

</details>

#### AC-4: is_readable returns true after write_byte

1. var u = MockUart
2. u write byte
   - Expected: u.is_readable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
var u = MockUart(buf: buf, head: 0)
u.write_byte(0x42)
expect(u.is_readable()).to_equal(true)
```

</details>

#### AC-4: read_byte returns the written byte

1. var u = MockUart
2. u write byte
   - Expected: b equals `0x43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
var u = MockUart(buf: buf, head: 0)
u.write_byte(0x43)
val b = u.read_byte()
expect(b).to_equal(0x43)
```

</details>

#### AC-4: is_readable returns false when buffer is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [u8] = []
val u = MockUart(buf: buf, head: 0)
expect(u.is_readable()).to_equal(false)
```

</details>

#### AC-4: is_writable always returns true for mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
val u = MockUart(buf: buf, head: 0)
expect(u.is_writable()).to_equal(true)
```

</details>

#### AC-4: write_bytes writes multiple bytes

1. var u = MockUart
2. u write bytes
   - Expected: u.buf.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
var u = MockUart(buf: buf, head: 0)
u.write_bytes([0x01, 0x02, 0x03])
expect(u.buf.len()).to_equal(3)
```

</details>

#### AC-4: try_read_byte returns Some when readable

1. var u = MockUart
2. u write byte
   - Expected: opt.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
var u = MockUart(buf: buf, head: 0)
u.write_byte(0x55)
val opt = u.try_read_byte()
expect(opt.is_some()).to_equal(true)
```

</details>

#### AC-4: try_read_byte returns None when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
val u = MockUart(buf: buf, head: 0)
val opt = u.try_read_byte()
expect(opt.is_none()).to_equal(true)
```

</details>

### AC-3/AC-4 HAL Spi trait

#### AC-4: transfer_byte returns the configured reply

1. var s = MockSpi
   - Expected: got equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MockSpi(last_sent: 0, reply: 0xAB)
val got = s.transfer_byte(0x12)
expect(got).to_equal(0xAB)
```

</details>

#### AC-4: is_busy returns false for mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = MockSpi(last_sent: 0, reply: 0)
expect(s.is_busy()).to_equal(false)
```

</details>

### AC-3/AC-4 HAL I2c trait

#### AC-4: write returns I2cResult.Ok for mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
val ic = MockI2c(data: data)
val res = ic.write(0x50, [0x01, 0x02])
expect(res == I2cResult.Ok).to_equal(true)
```

</details>

#### AC-4: read returns pre-loaded data and Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ic = MockI2c(data: [0xDE, 0xAD])
val result = ic.read(0x50, 2)
expect(result.is_ok()).to_equal(true)
val data = result.unwrap()
expect(data.len()).to_equal(2)
expect(data[0]).to_equal(0xDE)
```

</details>

#### AC-4: write_read returns Ok for mock

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wd: [u8] = []
val ic = MockI2c(data: [0xBE, 0xEF])
val result = ic.write_read(0x50, wd, 2)
expect(result.is_ok()).to_equal(true)
val data = result.unwrap()
expect(data.len()).to_equal(2)
expect(data[0]).to_equal(0xBE)
```

</details>

### AC-3/AC-4 HAL Timer trait

#### AC-4: init sets timer to not running

1. var t = MockTimer
2. t init
   - Expected: t.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: false, running: false, cnt: 0, period_us_val: 0)
t.init()
expect(t.is_running()).to_equal(false)
```

</details>

#### AC-4: start sets is_running to true

1. var t = MockTimer
2. t start
   - Expected: t.is_running() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: false, running: false, cnt: 0, period_us_val: 0)
t.start(1000, TimerMode.OneShot)
expect(t.is_running()).to_equal(true)
```

</details>

#### AC-4: stop sets is_running to false

1. var t = MockTimer
2. t stop
   - Expected: t.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: false, running: true, cnt: 0, period_us_val: 0)
t.stop()
expect(t.is_running()).to_equal(false)
```

</details>

#### AC-4: period returns the period set by start

1. var t = MockTimer
2. t start
   - Expected: t.period() equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: false, running: false, cnt: 0, period_us_val: 0)
t.start(5000, TimerMode.Periodic)
expect(t.period()).to_equal(5000)
```

</details>

#### AC-4: is_fired returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTimer(fired: false, running: false, cnt: 0, period_us_val: 0)
expect(t.is_fired()).to_equal(false)
```

</details>

#### AC-4: clear resets fired flag to false

1. var t = MockTimer
2. t clear
   - Expected: t.is_fired() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: true, running: false, cnt: 0, period_us_val: 0)
t.clear()
expect(t.is_fired()).to_equal(false)
```

</details>

#### AC-4: counter returns the value set by set_counter

1. var t = MockTimer
2. t set counter
   - Expected: t.counter() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MockTimer(fired: false, running: false, cnt: 0, period_us_val: 0)
t.set_counter(42)
expect(t.counter()).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
