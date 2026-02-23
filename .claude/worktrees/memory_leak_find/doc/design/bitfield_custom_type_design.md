# Bitfields with Custom Types: Design Document

**Date**: 2026-02-05
**Status**: Research & Design
**Related**: `doc/spec/units_part2.md`, `doc/design/baremetal_features_examples.md`

---

## Problem Statement

How do bitfields work with custom types when:
1. The type is **NOT designed** for bitfields (no bit-width specified)
2. The type **IS designed** for bitfields (max_value/bits specified)
3. How to **add bit-width** to a type that doesn't have one

---

## Current Design (from units_part2.md)

### Types Designed for Bitfields

Types can specify allowed bit representations via `repr:` block:

```simple
unit length(base: f64): m = 1.0, cm = 0.01, km = 1000.0:
    repr: f16, f32, f64, i8, i12, i16, i32, u8, u12, u16, u32

# Usage in bitfield
bitfield RobotArm(u64):
    x: cm:i12     # 12-bit signed centimeters
    y: cm:i12     # 12-bit signed centimeters
    z: cm:u10     # 10-bit unsigned centimeters
    angle: deg:u9 # 9-bit unsigned degrees
```

### Range-Based Inference

```simple
# Compiler infers bit-width from range
bitfield SensorData(u32):
    temp: celsius where range: -40..125     # Infers i8 (8 bits)
    humidity: pct where range: 0..100       # Infers u7 (7 bits)
```

---

## Scenario Analysis

### Scenario 1: Type NOT Designed for Bitfields

**Problem**: Using a type in bitfield that has no `repr:` block or bit-width info.

```simple
# Custom type with no repr block
struct UserId:
    value: i64

# ERROR: How many bits?
bitfield UserFlags(u64):
    user_id: UserId    # ERROR: UserId has no bit representation
    flags: u8
```

**Current Behavior**: Compile error - type not usable in bitfield.

### Scenario 2: Type IS Designed for Bitfields

**Problem**: Type has `repr:` block with allowed representations.

```simple
unit angle(base: f64): deg = 1.0, rad = 57.2958:
    repr: f32, f64, i9, i16, u9, u16

# OK: deg:u9 is in repr list
bitfield Servo(u32):
    angle: deg:u9    # 9-bit unsigned degrees (0-511)
```

**Current Behavior**: Works if repr is in allowed list.

### Scenario 3: Bounded/Range Type

**Problem**: Type has a known range but no explicit repr.

```simple
# Enum has implicit range (3 values = 2 bits)
enum Direction:
    North    # 0
    East     # 1
    South    # 2
    West     # 3

# Should work: enum has 4 variants = 2 bits needed
bitfield Movement(u8):
    direction: Direction   # Infer 2 bits from enum
    speed: u4              # 4 bits
```

---

## Proposed Solutions

### Solution 1: `BitRepr` Trait

Define a trait that types implement to be usable in bitfields:

```simple
trait BitRepr:
    const BIT_WIDTH: i32           # Required bits
    const IS_SIGNED: bool          # Signed or unsigned
    const MIN_VALUE: i64           # Minimum representable value
    const MAX_VALUE: i64           # Maximum representable value

    fn to_bits(self) -> u64        # Convert to raw bits
    fn from_bits(bits: u64) -> Self  # Convert from raw bits

# Auto-implemented for primitives
impl BitRepr for u8:
    const BIT_WIDTH = 8
    const IS_SIGNED = false
    const MIN_VALUE = 0
    const MAX_VALUE = 255

    fn to_bits(self) -> u64: self as u64
    fn from_bits(bits: u64) -> u8: bits as u8

# Auto-implemented for enums
impl BitRepr for Direction:
    const BIT_WIDTH = 2            # ceil(log2(4)) = 2
    const IS_SIGNED = false
    const MIN_VALUE = 0
    const MAX_VALUE = 3

    fn to_bits(self) -> u64:
        match self:
            North: 0
            East: 1
            South: 2
            West: 3

    fn from_bits(bits: u64) -> Direction:
        match bits:
            0: North
            1: East
            2: South
            3: West
            _: panic("Invalid direction bits")
```

**Usage in Bitfield:**

```simple
bitfield Movement(u8):
    direction: Direction   # Uses Direction.BIT_WIDTH = 2
    speed: u4              # Explicit 4 bits
    _reserved: 2           # Padding
```

### Solution 2: Explicit `bits` Attribute

Add bits explicitly at use site:

```simple
# Type without BitRepr
struct CustomId:
    value: i32

# Specify bits at use site
bitfield Record(u64):
    id: CustomId @bits(24)        # Force 24-bit representation
    flags: u8
    _reserved: 32

# Compiler generates bounds checking
# CustomId.value must fit in 24 bits (0..16777215 unsigned, or -8388608..8388607 signed)
```

### Solution 3: `Bounded` Types with Range

Types can declare their valid range:

```simple
# Bounded integer type
type Temperature = i32 where range: -273..10000

# Compiler knows: needs 15 bits (signed)
# ceil(log2(10273)) + 1 sign bit = 14 + 1 = 15 bits

bitfield Climate(u32):
    temp: Temperature      # Infers 15 bits from range
    humidity: u7           # 0-100%
    _reserved: 10
```

### Solution 4: `repr` Attribute on Any Type

Allow `repr` attribute on structs/types:

```simple
# Add repr to any struct
@repr(bits: 24, signed: false)
struct UserId:
    value: i64    # Internally i64, but serializes to 24 bits

# Now usable in bitfield
bitfield UserRecord(u64):
    user_id: UserId        # 24 bits (from @repr)
    permissions: u8        # 8 bits
    _reserved: 32
```

---

## Recommended Design

### Three-Tier System

#### Tier 1: Automatic (Types with Known Bounds)

Types that automatically work in bitfields:

| Type | Bit Width | How Determined |
|------|-----------|----------------|
| `u8`, `i8` | 8 | Primitive size |
| `u16`, `i16` | 16 | Primitive size |
| `bool` | 1 | Boolean |
| `enum` (N variants) | ceil(log2(N)) | Variant count |
| `T where range: A..B` | ceil(log2(B-A+1)) + sign | Range |
| `unit:repr` (e.g., `cm:u8`) | repr bits | Explicit repr |

```simple
enum Status:
    Idle      # 0
    Running   # 1
    Paused    # 2
    Error     # 3

bitfield DeviceState(u8):
    status: Status        # Auto: 2 bits (4 variants)
    enabled: bool         # Auto: 1 bit
    priority: u3          # Explicit: 3 bits
    _reserved: 2
```

#### Tier 2: Explicit Bits at Use Site

For types without automatic bit info:

```simple
struct SerialNumber:
    value: i64

# Use @bits at field level
bitfield Product(u64):
    serial: SerialNumber @bits(32)   # Explicit 32 bits
    batch: u16
    _reserved: 16
```

#### Tier 3: Type-Level Repr Declaration

Add bit representation to type definition:

```simple
# Option A: @repr attribute
@repr(bits: 20)
struct ProductId:
    value: i64

# Option B: BitRepr trait implementation
impl BitRepr for ProductId:
    const BIT_WIDTH = 20
    const IS_SIGNED = false
    const MIN_VALUE = 0
    const MAX_VALUE = 1048575

    fn to_bits(self) -> u64: self.value as u64
    fn from_bits(bits: u64) -> ProductId: ProductId(value: bits as i64)

# Option C: where clause in type definition
type ProductId = i64 where range: 0..1048575  # Infers u20
```

---

## Complete Example

```simple
# === Type Definitions ===

# Tier 1: Automatic from enum
enum Command:
    Nop
    Read
    Write
    Reset

# Tier 1: Automatic from range
type Temperature = i16 where range: -40..125   # Infers i8

# Tier 2: Will use @bits at use site
struct DeviceAddress:
    value: u32

# Tier 3: Type with explicit BitRepr
@repr(bits: 12, signed: false)
struct ChannelId:
    value: i32

# Unit type with repr block
unit voltage(base: f64): mV = 0.001, V = 1.0:
    repr: i12, i16, u12, u16

# === Bitfield Definition ===

bitfield ControlPacket(u64):
    # Tier 1: Automatic
    command: Command                  # 2 bits (4 variants)
    temp: Temperature                 # 8 bits (from range)
    voltage: mV:i12                   # 12 bits (from unit repr)

    # Tier 2: Explicit at use site
    device: DeviceAddress @bits(16)   # 16 bits (explicit)

    # Tier 3: From type repr
    channel: ChannelId                # 12 bits (from @repr)

    # Primitive
    flags: u8                         # 8 bits

    # Reserved/padding
    _reserved: 6                      # 6 bits

# Static assertions
static assert size_of<ControlPacket>() == 8  # 64 bits total
static assert ControlPacket.command.offset == 0
static assert ControlPacket.command.width == 2
static assert ControlPacket.temp.offset == 2
static assert ControlPacket.temp.width == 8

# === Usage ===

val packet = ControlPacket(
    command: Command.Write,
    temp: 25,
    voltage: 3300_mV,
    device: DeviceAddress(value: 0x1234) @bits(16),
    channel: ChannelId(value: 42),
    flags: 0xFF
)

# Access fields
val cmd = packet.command      # Command enum
val temp = packet.temp        # i8 value
val v = packet.voltage        # mV unit type

# Modify fields
packet.flags = 0x00

# Convert to raw
val raw: u64 = packet.to_raw()
val packet2 = ControlPacket.from_raw(raw)
```

---

## Bit Width Inference Rules

### Automatic Inference

| Source | Formula | Example |
|--------|---------|---------|
| **Unsigned range** `0..max` | ceil(log2(max+1)) | `0..255` → 8 bits |
| **Signed range** `min..max` | ceil(log2(max-min+1)) + 1 | `-128..127` → 8 bits |
| **Enum** (N variants) | ceil(log2(N)) | 4 variants → 2 bits |
| **Bool** | 1 | Always 1 bit |
| **Primitive** `uN`/`iN` | N | `u12` → 12 bits |

### Inference Examples

```simple
# From range
type A = i32 where range: 0..100       # u7 (7 bits)
type B = i32 where range: -50..50      # i8 (7 bits + sign)
type C = i32 where range: 0..1000      # u10 (10 bits)
type D = i32 where range: -500..500    # i11 (10 bits + sign)

# From enum
enum E1:      # 1 variant → 0 bits (but minimum 1)
    Only

enum E2:      # 2 variants → 1 bit
    A, B

enum E3:      # 3-4 variants → 2 bits
    A, B, C

enum E4:      # 5-8 variants → 3 bits
    A, B, C, D, E

# From unit repr
angle: deg:u9      # 9 bits (explicit)
length: cm:i12     # 12 bits (explicit)
```

---

## Error Messages

### Type Not Usable in Bitfield

```
error[E0501]: type `CustomType` cannot be used in bitfield
  --> example.spl:10:5
   |
10 |     data: CustomType
   |     ^^^^^^^^^^^^^^^^
   |
   = note: `CustomType` does not implement `BitRepr` trait
   = note: `CustomType` has no `@repr` attribute
   = help: add `@bits(N)` at use site: `data: CustomType @bits(16)`
   = help: or add `@repr(bits: N)` to type definition
   = help: or implement `BitRepr` trait for `CustomType`
```

### Explicit Bits Required

```
error[E0502]: bit width required for `DeviceAddress` in bitfield
  --> example.spl:10:5
   |
10 |     addr: DeviceAddress
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `DeviceAddress` has no automatic bit width
   = help: specify bits explicitly: `addr: DeviceAddress @bits(16)`
```

### Value Doesn't Fit

```
error[E0503]: value does not fit in bit representation
  --> example.spl:15:20
   |
15 |     serial: SerialNumber @bits(8)
   |                          ^^^^^^^^
   |
   = note: `SerialNumber` range is 0..4294967295 (32 bits needed)
   = note: @bits(8) only allows 0..255
   = help: use @bits(32) or constrain the type's range
```

---

## Summary

### How to Use Custom Types in Bitfields

| Scenario | Solution | Example |
|----------|----------|---------|
| Primitive type | Automatic | `flags: u8` |
| Enum | Automatic | `status: Status` |
| Bounded type | Automatic | `temp: Temperature` (with `where range`) |
| Unit with repr | Use repr syntax | `angle: deg:u9` |
| Unknown type | `@bits` at use | `data: Custom @bits(16)` |
| Type with `@repr` | Automatic | `id: ProductId` (has `@repr(bits: 20)`) |
| Implement trait | Automatic | `id: CustomId` (implements `BitRepr`) |

### Adding Bit Width to Types

| Method | Where | Example |
|--------|-------|---------|
| `@bits(N)` | Field use site | `data: MyType @bits(16)` |
| `@repr(bits: N)` | Type definition | `@repr(bits: 20) struct MyType` |
| `where range: A..B` | Type definition | `type MyType = i32 where range: 0..1000` |
| `impl BitRepr` | Trait impl | `impl BitRepr for MyType: ...` |
| `repr:` block | Unit family | `unit length(...): repr: u8, u12, u16` |

### Priority (Highest to Lowest)

1. `@bits(N)` at field use site
2. `@repr(bits: N)` on type definition
3. `impl BitRepr` trait
4. `where range:` constraint
5. Unit `repr:` block
6. Automatic (enum variants, primitives)

---

## Range Constraints and Checking

### All Approaches Include:

1. **Compile-time checks** (static) - when value is known at compile time
2. **Debug mode runtime checks** - when value is only known at runtime
3. **Release mode behavior** - configurable (checked, saturate, wrap, unchecked)

### Compile-Time Checks (Static)

```simple
bitfield Sensor(u16):
    temp: i8              # Range: -128..127
    humidity: u7          # Range: 0..127

# Compile-time check: literal value
val sensor = Sensor(
    temp: 200,            # ERROR: 200 > 127 (compile-time)
    humidity: 50          # OK
)

# Compile-time check: const expression
const MAX_TEMP = 150
val sensor2 = Sensor(
    temp: MAX_TEMP,       # ERROR: 150 > 127 (compile-time)
    humidity: 50
)

# Static assertion on field range
static assert Sensor.temp.min == -128
static assert Sensor.temp.max == 127
static assert Sensor.humidity.min == 0
static assert Sensor.humidity.max == 127
```

### Debug Mode Runtime Checks

```simple
fn read_sensor() -> i32:
    # Returns value only known at runtime
    external_sensor_read()

fn update_sensor(sensor: mut Sensor):
    val temp = read_sensor()

    # Debug mode: runtime range check
    # - Panics if temp < -128 or temp > 127
    # Release mode: depends on overflow behavior setting
    sensor.temp = temp

# Explicit overflow behavior
fn update_sensor_safe(sensor: mut Sensor):
    val temp = read_sensor()

    # Option 1: Checked (panic on overflow, both debug and release)
    sensor.temp = temp @checked

    # Option 2: Saturate (clamp to range)
    sensor.temp = temp @saturate    # Clamps to -128..127

    # Option 3: Wrap (modular arithmetic)
    sensor.temp = temp @wrap        # Wraps around

    # Option 4: Unchecked (no check, undefined if out of range)
    sensor.temp = temp @unchecked   # Dangerous! No check
```

### Per-Field Overflow Behavior

```simple
bitfield SensorData(u32):
    # Default: checked in debug, unchecked in release
    temp: i8

    # Always checked (debug and release)
    humidity: u7 @checked

    # Always saturate
    pressure: u10 @saturate

    # Always wrap (modular)
    counter: u8 @wrap

# Usage
val data = SensorData()
data.temp = 200           # Debug: panic, Release: undefined
data.humidity = 200       # Always panic (checked)
data.pressure = 2000      # Becomes 1023 (saturate to max)
data.counter = 300        # Becomes 44 (300 mod 256)
```

### Type-Level Overflow Behavior

```simple
# Type with default overflow behavior
@repr(bits: 12, overflow: saturate)
struct Measurement:
    value: i32

# Unit with overflow behavior
unit temperature(base: f64): celsius = 1.0:
    repr: i8 @checked, i16, u8 @saturate

# Usage
bitfield Climate(u32):
    temp: celsius:i8          # Uses @checked from repr
    alt_temp: celsius:u8      # Uses @saturate from repr
```

### Compile-Time vs Runtime Summary

| Scenario | Check Type | Behavior |
|----------|------------|----------|
| Literal value in range | Compile-time | OK |
| Literal value out of range | Compile-time | **Error** |
| Const expression in range | Compile-time | OK |
| Const expression out of range | Compile-time | **Error** |
| Runtime value (debug) | Runtime | **Panic** (default) |
| Runtime value (release) | Runtime | Per-field setting |
| `@checked` | Runtime (always) | **Panic** |
| `@saturate` | Runtime (always) | Clamp to range |
| `@wrap` | Runtime (always) | Modular arithmetic |
| `@unchecked` | None | Undefined behavior |

### Configuration in `__init__` or `simple.sdn`

```simple
# Module-level default (__init__)
__init__:
    bitfield_overflow = "checked"    # Default for all bitfields in module
```

```sdn
# Project-level default (simple.sdn)
[bitfield]
overflow_default = "checked"         # "checked", "saturate", "wrap", "unchecked"

[bitfield.profiles]
debug:
    overflow_default = "checked"     # Panic on overflow in debug
release:
    overflow_default = "saturate"    # Clamp in release (safe)

embedded:
    overflow_default = "wrap"        # Modular arithmetic (predictable)
```

### Complete Example with All Checks

```simple
# Type definitions with range constraints
@repr(bits: 12, signed: true, overflow: checked)
struct Position:
    value: i32    # Must fit in 12 bits signed: -2048..2047

type Temperature = i16 where range: -40..125   # i8, auto checked

enum Mode: Off, Low, Medium, High              # 2 bits, always valid

# Bitfield with mixed overflow behaviors
bitfield RobotState(u64):
    # Compile-time checked (enum always valid)
    mode: Mode                       # 2 bits

    # Compile-time + debug runtime checked
    temp: Temperature                # 8 bits, checked

    # Always checked (panic if out of range)
    x: Position                      # 12 bits, @checked from type

    # Saturate (clamp to range)
    y: i12 @saturate                 # 12 bits, clamp

    # Wrap (modular)
    sequence: u8 @wrap               # 8 bits, wrap

    # Reserved
    _reserved: 22

# Usage with compile-time checks
val robot = RobotState(
    mode: Mode.High,                 # OK: valid enum
    temp: 25,                        # OK: in range -40..125
    x: Position(value: 1000),        # OK: in range -2048..2047
    y: 0,
    sequence: 0
)

# Compile-time errors
val bad = RobotState(
    mode: Mode.High,
    temp: 200,                       # ERROR: 200 > 125 (compile-time)
    x: Position(value: 3000),        # ERROR: 3000 > 2047 (compile-time)
    y: 0,
    sequence: 0
)

# Runtime checks
fn update_robot(robot: mut RobotState, sensor_temp: i32, pos_x: i32):
    robot.temp = sensor_temp         # Debug: panic if out of range
    robot.x = Position(value: pos_x) # Always: panic if out of range (@checked)
    robot.y = pos_x                  # Always: saturate to -2048..2047
    robot.sequence = robot.sequence + 1  # Always: wraps at 255→0
```

### Static Assertions for Verification

```simple
# Verify bitfield layout at compile time
static assert size_of<RobotState>() == 8
static assert RobotState.mode.offset == 0
static assert RobotState.mode.width == 2
static assert RobotState.temp.offset == 2
static assert RobotState.temp.width == 8
static assert RobotState.x.offset == 10
static assert RobotState.x.width == 12

# Verify ranges
static assert RobotState.temp.min == -40
static assert RobotState.temp.max == 125
static assert RobotState.x.min == -2048
static assert RobotState.x.max == 2047
static assert RobotState.y.min == -2048
static assert RobotState.y.max == 2047
static assert RobotState.sequence.min == 0
static assert RobotState.sequence.max == 255
```
