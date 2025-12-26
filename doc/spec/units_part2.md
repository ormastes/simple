# Unit Types Specification - Part 2: Advanced Features

**Part of:** [Unit Types](./units_part1.md)

---


### 7.5 Compound Units

Compound units represent derived quantities like velocity (length/time) or force (mass × acceleration):

```ebnf
compound_unit_def = "unit" IDENT "=" unit_expr [ ":" NEWLINE INDENT arithmetic_block DEDENT ]

unit_expr = unit_term (("*" | "/") unit_term)*
unit_term = IDENT [ "^" INTEGER ]
```

**Examples:**

```simple
# Velocity = length / time
unit velocity = length / time:
    allow add(velocity) -> velocity
    allow sub(velocity) -> velocity
    allow mul(f64) -> velocity
    allow div(f64) -> velocity

    # velocity * time -> length
    allow mul(time) -> length

# Acceleration = velocity / time = length / time²
unit acceleration = length / time^2:
    allow add(acceleration) -> acceleration
    allow sub(acceleration) -> acceleration
    allow mul(f64) -> acceleration

    # acceleration * time -> velocity
    allow mul(time) -> velocity

# Force = mass * acceleration (Newton's second law)
unit mass(base: f64): kg = 1.0, g = 0.001, lb = 0.453592

unit force = mass * acceleration:
    allow add(force) -> force
    allow sub(force) -> force
    allow mul(f64) -> force
    allow div(f64) -> force
```

### 7.6 Arithmetic Type Checking

The compiler enforces these rules:

| Expression | Rule Required | Example |
|------------|---------------|---------|
| `a + b` | `allow add(typeof(b)) -> result` in `typeof(a)` | `length + length` |
| `a - b` | `allow sub(typeof(b)) -> result` | `length - length` |
| `a * b` | `allow mul(typeof(b)) -> result` | `length * f64` |
| `a / b` | `allow div(typeof(b)) -> result` | `length / time -> velocity` |
| `-a` | `allow neg -> result` | `-5_km` |
| `a.abs()` | `allow abs -> result` | `(-5_km).abs()` |

**Valid Operations:**

```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow mul(f64) -> length

unit time(base: f64): s = 1.0, hr = 3600.0:
    allow add(time) -> time

let d1 = 5_km
let d2 = 3_km
let total = d1 + d2      # OK: length + length -> length
let scaled = d1 * 2.0    # OK: length * f64 -> length

let t1 = 2_hr
let t2 = 1_hr
let duration = t1 + t2   # OK: time + time -> time
```

**Invalid Operations (Compile Errors):**

```simple
let invalid = d1 + t1    # ERROR: cannot add length + time
let bad = d1 * d2        # ERROR: length * length not allowed (need explicit rule)
```

### 7.7 Automatic Unit Conversion in Operations

Operations between same-family units auto-convert to base unit:

```simple
let d1 = 5_km            # 5000 meters internally
let d2 = 3000_m          # 3000 meters
let total = d1 + d2      # 8000 meters (base unit)

# Result is in base unit; convert as needed
print total.to_km()      # 8.0
print total.to_m()       # 8000.0
```

### 7.8 Compound Unit Resolution

When compound units are defined, the compiler creates implicit conversion rules:

```simple
unit velocity = length / time

# These operations become valid:
let d = 100_km
let t = 2_hr
let v = d / t            # Produces velocity type

let d2 = v * 3_hr        # velocity * time -> length (300 km)
```

### 7.9 Custom Unit Functions

Custom functions enable domain-specific operations that may not fit standard arithmetic:

```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow mul(f64) -> length

    # Logarithm of length (returns raw value - dimensionless)
    fn log(self) -> f64:
        return log(self.value())

    # Exponential (returns raw value)
    fn exp(self) -> f64:
        return exp(self.value())

    # Square root (could return length^0.5, but simplified to f64)
    fn sqrt(self) -> f64:
        return sqrt(self.value())

    # Custom conversion with unit transformation
    fn squared(self) -> area:
        return area.from_base(self.value() * self.value())

# Usage
let d = 100_m
let log_d = d.log()           # f64: ~4.605
let area = d.squared()        # area type
```

### 7.10 Error Messages

Clear error messages help users understand and fix type mismatches:

```
error: cannot add `length` and `time`
  --> example.spl:10:15
   |
10 | let x = d1 + t1
   |              ^^ `time` cannot be added to `length`
   |
   = help: `length` only allows: add(length) -> length
   = note: different unit families cannot be combined

error: multiplication not allowed for `user_id`
  --> example.spl:15:12
   |
15 | let x = id * 2
   |            ^ `user_id` has no arithmetic rules defined
   |
   = help: define arithmetic rules in the unit family, or use `.value()` to access raw value
```

---

## 8. Bit-Limited Unit Representations

### 8.1 Overview

Units can specify **storage representations** with explicit bit widths, enabling:
- Compact storage in bitfields and packed structures
- Debug-mode boundary checking for overflow detection
- App-level customization of unit storage without modifying library definitions

**Design Principles:**
- Library defines allowed representations via `repr:` block
- App chooses specific representation at use site
- Compact `:` syntax for simple cases
- Full `where` clause for complex constraints (range, overflow behavior)

### 8.2 Grammar

```ebnf
# Unit family with repr block (lib level)
unit_family_def = "unit" IDENT "(" "base" ":" type ")" ":" variant_list
                  [ ":" NEWLINE INDENT unit_body DEDENT ]

unit_body = (arithmetic_rule | repr_block | custom_fn)*

repr_block = "repr" ":" repr_list
repr_list = repr_type ("," repr_type)*
repr_type = ("u" | "i" | "f") DIGITS

# Type with repr constraint (app level)
# In type position, use bare suffix (no underscore): cm, km, deg
# In literal position, use underscore: 100_cm, 50_km, 360_deg
type_with_repr = unit_suffix [ ":" repr_type ] [ "where" constraints ]
               | unit_suffix "where" constraints

unit_suffix    = IDENT    # lowercase unit suffix: cm, km, deg, uid

# One-pass parsing (LL(2))
# In type position after IDENT:
#   1. Lookahead(1): is next token ":"?
#      - No: simple type (cm, UserId)
#      - Yes: check lookahead(2)
#   2. Lookahead(2): is token after ":" a repr_type?
#      - Yes: unit_with_repr (cm:u8)
#      - No: end of type (":" belongs to outer construct)

constraints = constraint ("," constraint)*
constraint = "range" ":" range_expr
           | "checked"                    # debug boundary check (panic on overflow)
           | "saturate"                   # clamp to min/max on overflow
           | "wrap"                       # modular arithmetic on overflow
           | "default" ":" expr           # default value
```

### 8.3 Library-Level: Repr Block

Unit families declare allowed representations in a `repr:` block:

```simple
unit length(base: f64): m = 1.0, cm = 0.01, km = 1000.0:
    # Arithmetic rules
    allow add(length) -> length
    allow sub(length) -> length
    allow mul(f64) -> length
    allow div(f64) -> length

    # Allowed representations
    repr: f16, f32, f64, i8, i12, i16, i32, u8, u12, u16, u32

unit time(base: f64): s = 1.0, ms = 0.001, us = 0.000001:
    allow add(time) -> time
    allow sub(time) -> time
    repr: f32, f64, i16, i32, i64, u16, u32, u64

unit angle(base: f64): deg = 1.0, rad = 57.2958:
    allow add(angle) -> angle
    allow sub(angle) -> angle
    repr: f32, f64, i9, i16, u9, u16
```

**Repr Types:**

| Prefix | Meaning | Examples |
|--------|---------|----------|
| `u` | Unsigned integer | `u8`, `u12`, `u16`, `u24`, `u32` |
| `i` | Signed integer | `i8`, `i12`, `i16`, `i24`, `i32` |
| `f` | Floating point | `f16`, `f32`, `f64` |

### 8.4 App-Level: Compact Syntax

Use colon `:` for simple repr specification. In type positions, use the **bare unit suffix** (no underscore prefix):

```simple
# Type aliases - bare suffix in type position
type Cm8 = cm:u8            # 8-bit unsigned centimeters
type Cm12 = cm:i12          # 12-bit signed centimeters
type Deg9 = deg:u9          # 9-bit unsigned degrees (0-511)

# Variable declarations - bare suffix:repr
let width: cm:u16 = 100_cm
let height: cm:u8 = 50_cm
let angle: deg:u9 = 360_deg

# Default repr (uses family base type)
let distance: cm = 1000_cm     # f64 (base type)

# Note: Literals still use underscore: 100_km, 50_cm
# Types use bare suffix: km, cm:u8, deg:u9
```

**Syntax distinction:**
| Context | Syntax | Example |
|---------|--------|---------|
| Literal (value) | `number_suffix` | `100_km`, `50_cm` |
| Type position | `suffix` or `suffix:repr` | `km`, `cm:u8` |

### 8.5 App-Level: Where Clause

Use `where` for complex constraints:

```simple
# Range constraint (compiler infers bit width)
let x: cm where range: 0..1000 = 500_cm            # infers u10

# Range with signed values
let offset: cm where range: -500..500 = 0_cm       # infers i10

# Explicit repr + debug checking
let y: cm:u8 where checked = 50_cm                 # panic on overflow in debug

# Overflow behavior options
let z: cm:u8 where saturate = 200_cm               # clamp to 0-255
let w: deg:u9 where wrap = 400_deg                 # wrap around (modular)

# Combined constraints
let pos: cm where range: 0..1000, checked = 500_cm
let angle: deg:u9 where wrap, default: 0_deg = get_angle()
```

### 8.6 Overflow Behavior

| Behavior | Keyword | Debug Mode | Release Mode |
|----------|---------|------------|--------------|
| Default | (none) | Panic | Undefined |
| Checked | `checked` | Panic | Panic |
| Saturate | `saturate` | Clamp | Clamp |
| Wrap | `wrap` | Modular | Modular |

```simple
let a: cm:u8 = 300_cm                     # Debug: panic, Release: undefined
let b: cm:u8 where checked = 300_cm       # Always panic
let c: cm:u8 where saturate = 300_cm      # Value becomes 255
let d: cm:u8 where wrap = 300_cm          # Value becomes 44 (300 mod 256)
```

### 8.7 Range Inference

When using `range:`, the compiler infers the minimum bit width:

| Range | Inferred Type | Bits |
|-------|---------------|------|
| `0..255` | `u8` | 8 |
| `0..1000` | `u10` | 10 |
| `0..65535` | `u16` | 16 |
| `-128..127` | `i8` | 8 |
| `-500..500` | `i10` | 10 |
| `-32768..32767` | `i16` | 16 |

```simple
# Compiler calculates: ceil(log2(1001)) = 10 bits needed
let room_size: cm where range: 0..1000 = 500_cm    # u10

# Compiler calculates: ceil(log2(1001)) + 1 sign bit = 11 bits
let offset: cm where range: -500..500 = 0_cm       # i11
```

### 8.8 Conversions Between Representations

```simple
let a: cm:u8 = 100_cm
let b: cm:u16 = a.widen()        # Explicit widening (always safe)
let c: cm:u8 = b.narrow()        # Explicit narrowing (checked in debug)

# Implicit widening is allowed
let d: cm:u16 = a                # OK: u8 → u16 implicit

# Implicit narrowing is NOT allowed
# let e: cm:u8 = b               # ERROR: use .narrow() or .saturate()

# Safe narrowing options
let f: cm:u8 = b.narrow()        # Panics if out of range
let g: cm:u8 = b.saturate()      # Clamps to 0-255
let h: cm:u8 = b.wrap()          # Modular arithmetic
```

### 8.9 Arithmetic with Different Representations

When operating on units with different representations, the result uses the wider type:

```simple
let a: cm:u8 = 100_cm
let b: cm:u16 = 200_cm
let c = a + b                    # Result type: cm:u16

let d: cm:i8 = -50_cm
let e: cm:u8 = 100_cm
let f = d + e                    # Result type: cm:i16 (signed + unsigned → signed wider)
```

### 8.10 Usage in Bitfields

See [Data Structures - Bitfields](data_structures.md#bitfields) for bitfield-specific syntax.

```simple
bitfield RobotArm:
    x: cm:i12           # 12-bit signed
    y: cm:i12
    z: cm:u10           # 10-bit unsigned
    angle: deg:u9       # 9-bit unsigned

bitfield SensorData:
    temp: celsius where range: -40..125       # infers i8
    humidity: pct where range: 0..100         # infers u7
    pressure: hpa:u16 where checked
```

---

## 9. Lint Attributes and Enforcement

### 9.1 The `primitive_api` Lint

The `primitive_api` lint controls warnings for bare primitives in public APIs.

**Levels:**
- `warn` (default) - Emit warning, continue compilation
- `deny` - Treat as compile error
- `allow` - Suppress entirely

### 9.2 The `bare_string` Lint

The `bare_string` lint controls warnings for bare `str`/`String` types in public APIs. String values should use semantic unit types like `FilePath`, `Url`, `IpAddr`, etc.

**Levels:**
- `warn` (default) - Emit warning, continue compilation
- `deny` - Treat as compile error
- `allow` - Suppress entirely

**Why strings need semantic types:**
- `"/path/to/file"` is not just a string - it's a `FilePath`
- `"192.168.1.1"` is not just a string - it's an `IpAddr`
- `"https://example.com"` is not just a string - it's an `HttpUrl`

**Exemptions** (`#[allow(bare_string)]`):
- `std.fmt` - formatting arbitrary values
- `std.log` - logging messages
- Low-level parsing utilities

```simple
# WARNING: Bare string
pub fn read_config(path: str) -> Config:     # Warning!
    ...

# OK: Semantic type
pub fn read_config(path: FilePath) -> Config:
    ...

# Exemption for logging
#[allow(bare_string)]
pub fn log(message: str):
    ...
```

### 9.3 Attribute Syntax

```simple
# Directory-level (in __init__.spl, applies to entire directory tree)
#[deny(primitive_api)]
#[deny(bare_string)]
mod std

# Module-level (in __init__.spl)
#[deny(primitive_api)]
mod strict_module

# Item-level (in any .spl file)
#[allow(primitive_api)]
pub fn raw_operation(x: i64) -> i64:   # No warning for this function
    ...

#[deny(primitive_api)]
pub fn strict_function(x: i64) -> i64: # Error for this function
    ...
```

**Directory-level lint inheritance:**

When `#[deny(primitive_api)]` is placed in a directory's `__init__.spl`, it applies to:
- All files directly in that directory
- All child directories (recursively, unless overridden)

### 9.4 Project Configuration (simple.toml)

```toml
[lint]
primitive_api = "warn"     # Default behavior
bare_string = "warn"       # NEW: warn on bare strings in public APIs
bare_bool = "warn"         # Warn on bool parameters

# Strict mode
# primitive_api = "deny"
# bare_string = "deny"
# bare_bool = "deny"
```

### 9.5 Standard Library Policy

The standard library declares strict lints in its root `__init__.spl`:

```simple
# std/__init__.spl
#[deny(primitive_api)]
#[deny(bare_string)]
#[deny(bare_bool)]
mod std

pub mod core
pub mod units
pub mod io
pub mod net
# ... all child modules inherit the deny settings
```

All stdlib modules inherit these settings through `__init__.spl` attribute inheritance:
- Any bare primitive in public API is a compile ERROR
- Any bare string in public API is a compile ERROR
- Any bare bool in public API is a compile ERROR
- This ensures stdlib has zero type-safety issues

**Result:**
- User code: warnings by default (educational, non-blocking)
- Standard library: errors (strict enforcement, zero tolerance)

### 9.6 Recommended Project Settings

| Project Type | Setting | Rationale |
|--------------|---------|-----------|
| New project | `deny` all | Start strict, build good habits |
| Library/SDK | `deny` all | Public APIs should be semantic |
| Application | `warn` all | Flexibility for internal code |
| Legacy migration | `allow` | Gradual adoption |
| Standard library | `deny` all | Exemplary code quality |

### 9.7 Related Lints Summary

| Lint | Default | Description |
|------|---------|-------------|
| `primitive_api` | warn | Bare primitives (`i32`, `f64`, etc.) in public APIs |
| `bare_string` | warn | Bare `str`/`String` in public APIs |
| `bare_bool` | warn | Bool parameters (suggest enum) |

**Note:** Implicit `nil` (nullable without `Option[T]`) is always a compile error and cannot be configured. This is a language rule, not a lint.

```toml
# simple.toml - strict mode (recommended for new projects)
[lint]
primitive_api = "deny"
bare_string = "deny"
bare_bool = "deny"
```

---

## 10. Migration Guide

### 10.1 From Bare Primitives

```simple
# Before
fn create_user(id: i64, age: i32, active: bool) -> User:
    ...

# After
fn create_user(id: UserId, age: Age, status: UserStatus) -> User:
    ...

# Define the types
unit UserId: i64 as uid
unit Age: i32 as age

enum UserStatus:
    Active
    Inactive
    Pending
```

### 10.2 From Bare Strings

```simple
# Before
fn read_file(path: str) -> Bytes:
    ...

fn connect(host: str, port: i32) -> Connection:
    ...

fn fetch_url(url: str) -> Response:
    ...

# After
fn read_file(path: FilePath) -> Bytes:
    ...

fn connect(host: Host, port: Port) -> Connection:
    ...

fn fetch_url(url: HttpUrl) -> Response:
    ...

# Call site with unit suffixes
let data = read_file("/etc/config.json"_file)
let conn = connect("example.com"_host, 443_port)
let resp = fetch_url("https://api.example.com"_http)
```

### 10.3 From Nullable Returns

```simple
# Before
fn find_user(id: i64) -> User:  # Returns nil if not found
    ...

# After
fn find_user(id: UserId) -> Option[User]:
    match lookup(id):
        case found: Some(found)
        case _: None
```

### 10.4 From Boolean Parameters

```simple
# Before
fn configure(enabled: bool, visible: bool, required: bool):
    ...

# After
fn configure(enabled: Enabled, visibility: Visibility, requirement: Required):
    ...

# Call site - much clearer!
configure(Enabled.Yes, Visibility.Hidden, Required.Optional)
```

---

## 11. Multi-Value Input Syntax

### 11.1 Overview

Simple introduces **underscore-separated literal syntax** for types that represent multiple values (coordinates, vectors, rectangles, etc.). This reduces verbosity and improves readability for common graphics, game, and scientific computing patterns.

**Design Principles:**
- Underscore separates component values: `100_200_loc` = `Loc2(100, 200)`
- Suffix determines the type: `_loc`, `_vec3`, `_rect`, `_m2` (meters 2D)
- Dimension is explicit in suffix: 2D is default (no number), 3D uses `3` suffix
- Works with both built-in types and user-defined custom types
- Integrates with physical units for dimensional analysis

### 11.2 Grammar

```ebnf
# Multi-value literal syntax
multi_value_literal = value_part ("_" value_part)* "_" type_suffix

value_part = NUMBER | FLOAT
type_suffix = IDENT [ DIGIT ]    # e.g., loc, loc3, vec2, m2, m3

# Examples parsed:
# 100_200_loc       → values=[100, 200], suffix="loc"
# 1_2_3_vec3        → values=[1, 2, 3], suffix="vec3"
# 0_0_100_50_rect   → values=[0, 0, 100, 50], suffix="rect"
# 10_20_30_m3       → values=[10, 20, 30], suffix="m3" (3D meters)
```

### 11.3 Built-in Multi-Value Types

| Type | Suffix | Arity | Example | Description |
|------|--------|-------|---------|-------------|
| `Loc2` | `_loc` | 2 | `100_200_loc` | 2D location (x, y) |
| `Loc3` | `_loc3` | 3 | `1_2_3_loc3` | 3D location (x, y, z) |
| `Size2` | `_size` | 2 | `50_30_size` | 2D size (width, height) |
| `Size3` | `_size3` | 3 | `10_20_30_size3` | 3D size (w, h, d) |
| `Vec2` | `_vec2` | 2 | `1.5_2.0_vec2` | 2D float vector |
| `Vec3` | `_vec3` | 3 | `1_0_0_vec3` | 3D float vector |
| `Vec4` | `_vec4` | 4 | `1_0_0_1_vec4` | 4D float vector (RGBA, quaternion) |
| `Rect` | `_rect` | 4 | `0_0_100_50_rect` | Rectangle (x, y, width, height) |
| `Box` | `_box` | 6 | `0_0_0_10_10_10_box` | 3D box (x, y, z, w, h, d) |
| `Color` | `_rgb` | 3 | `255_128_0_rgb` | RGB color (0-255) |
| `Color` | `_rgba` | 4 | `255_128_0_255_rgba` | RGBA color |

### 11.4 Naming Convention

**Rule:** 2D is the default (no dimension suffix), 3D uses explicit `3` suffix.

| Dimension | Convention | Examples |
|-----------|------------|----------|
| 2D (default) | No number or `2` | `_loc`, `_size`, `_vec2` |
| 3D | Suffix with `3` | `_loc3`, `_size3`, `_vec3` |
| 4D | Suffix with `4` | `_vec4`, `_quat` |

```simple
# 2D is default (most common in UI/graphics)
pos = 100_200_loc           # Loc2(100, 200)
size = 50_30_size           # Size2(50, 30)

# 3D is explicit
pos3d = 1_2_3_loc3          # Loc3(1, 2, 3)
size3d = 10_20_30_size3     # Size3(10, 20, 30)
```

### 11.5 Method Chaining on Literals

Multi-value literals support method chaining:

```simple
# Chain methods on literals
rect = 100_100_200_50_rect.color(Color.blue).rounded(5)
pos = 0_0_0_loc3.offset(1, 0, 0)
vec = 1_0_0_vec3.normalize()

# Fluent API style
button_bounds = 10_10_100_30_rect
    .padded(5)
    .centered_in(parent)
```

### 11.6 Multi-Value Units with Physical Dimensions

Units integrate with multi-value syntax for dimensional analysis:

```simple
# Scalar units (single value)
distance = 100_m              # 100 meters (scalar)
time = 5_s                    # 5 seconds

# Multi-value units with dimension suffix
position = 100_200_m2         # Position2D(100m, 200m)
position3d = 10_20_30_m3      # Position3D(10m, 20m, 30m)
velocity = 5_10_m_per_s2      # Velocity2D(5 m/s, 10 m/s)

# Pixel units for screen coordinates
screen_pos = 100_200_px2      # 2D position in pixels
viewport = 0_0_1920_1080_px_rect  # Rectangle in pixels
```

**Unit Dimension Suffix Convention:**

| Category | Scalar | 2D | 3D | Example |
|----------|--------|-------|-------|---------|
| Length | `_m`, `_cm`, `_px` | `_m2`, `_px2` | `_m3` | `100_200_px2` |
| Velocity | `_m_per_s` | `_m_per_s2` | `_m_per_s3` | `5_10_m_per_s2` |
| Angle | `_deg`, `_rad` | `_deg2` | `_deg3` | `45_90_deg2` |
| Force | `_N` | `_N2` | `_N3` | `1_2_3_N3` |

### 11.7 Implementation: FromLiteral Trait

Types support multi-value literals by implementing the `FromLiteral` trait:

```simple
trait FromLiteral:
    const SUFFIX: str          # Literal suffix (e.g., "loc", "vec3")
    const ARITY: int | Range   # Number of values expected

    fn from_parts(parts: [f64]) -> Self

# Built-in implementation
impl FromLiteral for Loc2:
    const SUFFIX = "loc"
    const ARITY = 2

    fn from_parts(parts: [f64; 2]) -> Self:
        Loc2(parts[0], parts[1])

impl FromLiteral for Vec3:
    const SUFFIX = "vec3"
    const ARITY = 3

    fn from_parts(parts: [f64; 3]) -> Self:
        Vec3(parts[0], parts[1], parts[2])
```

---

## 12. Custom Type Literal Suffixes

### 12.1 Overview

User-defined types can support multi-value underscore syntax by implementing the `FromLiteral` trait. This enables domain-specific types to use the same compact literal syntax as built-in types.

### 12.2 Defining Custom Literal Types

```simple
# Define a custom type
struct Quaternion:
    w: f32
    x: f32
    y: f32
    z: f32

# Implement multi-value literal support
impl FromLiteral for Quaternion:
    const SUFFIX = "quat"      # Enables: 1_0_0_0_quat
    const ARITY = 4            # Requires exactly 4 values

    fn from_parts(parts: [f32; 4]) -> Self:
        Quaternion(parts[0], parts[1], parts[2], parts[3])

# Usage
rotation = 1_0_0_0_quat              # Quaternion(1, 0, 0, 0) - identity
rotation = 0.707_0_0.707_0_quat      # 90° rotation around Y
```

### 12.3 Variadic Arity (Optional Components)

Types can accept a range of values using `Range` arity:

```simple
# Point with optional z coordinate
struct Point:
    x: f32
    y: f32
    z: f32 = 0.0                     # Default z for 2D

impl FromLiteral for Point:
    const SUFFIX = "pt"
    const ARITY = 2..3               # Accepts 2 or 3 values

    fn from_parts(parts: [f32]) -> Self:
        match parts.len():
            2 => Point(parts[0], parts[1], 0.0)
            3 => Point(parts[0], parts[1], parts[2])

# Usage
pos = 100_200_pt                     # Point(100, 200, 0)
pos = 100_200_50_pt                  # Point(100, 200, 50)

# CSS-style margin (1-4 values)
struct Margin:
    top: f32
    right: f32
    bottom: f32
    left: f32

impl FromLiteral for Margin:
    const SUFFIX = "margin"
    const ARITY = 1..4

    fn from_parts(parts: [f32]) -> Self:
        match parts.len():
            1 => Margin(parts[0], parts[0], parts[0], parts[0])      # all same
            2 => Margin(parts[0], parts[1], parts[0], parts[1])      # vertical, horizontal
            3 => Margin(parts[0], parts[1], parts[2], parts[1])      # top, horizontal, bottom
            4 => Margin(parts[0], parts[1], parts[2], parts[3])      # all different

# Usage
m = 10_margin                        # Margin(10, 10, 10, 10)
m = 10_20_margin                     # Margin(10, 20, 10, 20)
m = 10_20_30_margin                  # Margin(10, 20, 30, 20)
m = 10_20_30_40_margin               # Margin(10, 20, 30, 40)
```

### 12.4 Custom Type Registry

| Custom Type | Suffix | Arity | Example | Description |
|-------------|--------|-------|---------|-------------|
| `Quaternion` | `_quat` | 4 | `1_0_0_0_quat` | w, x, y, z rotation |
| `Tile` | `_tile` | 2-3 | `5_3_tile`, `5_3_0_tile` | x, y, optional layer |
| `Point` | `_pt` | 2-3 | `100_200_pt` | Optional z |
| `Margin` | `_margin` | 1-4 | `10_margin`, `10_20_margin` | CSS-style |
| `HSL` | `_hsl` | 3 | `180_100_50_hsl` | Hue, Saturation, Lightness |
| `HSLA` | `_hsla` | 4 | `180_100_50_100_hsla` | HSL + Alpha |

### 12.5 Unit-Aware Custom Types

Custom types can integrate with the unit system for type-safe dimensional analysis:

```simple
import std.units

# Custom type with unit constraint
struct Velocity2D[U: LengthPerTime]:
    x: U
    y: U

impl[U: LengthPerTime] FromLiteral for Velocity2D[U]:
    const SUFFIX = U.suffix + "2"    # e.g., "m_per_s2"
    const ARITY = 2

    fn from_parts(parts: [f32; 2]) -> Self:
        Velocity2D(U.new(parts[0]), U.new(parts[1]))

# Usage
vel = 5_10_m_per_s2                  # Velocity2D(5 m/s, 10 m/s)

# Physics simulation with unit-checked math
fn update_position(pos: Position3D[m], vel: Velocity3D[m_per_s], dt: Duration[s]) -> Position3D[m]:
    pos + vel * dt                   # Compile-time unit checking
```

### 12.6 Graphics Integration Example

```simple
# Graphics primitives with units
viewport = 0_0_1920_1080_px_rect     # Viewport in pixels
world_box = 0_0_0_100_100_50_m_box   # World bounding box in meters

# Conversion between unit systems
screen_pos = world_pos.to_px(camera) # meters → pixels
world_pos = screen_pos.to_m(camera)  # pixels → meters

# Immediate mode with units
with im:
    rect(100_100_200_50_px_rect.color(Color.blue))
    line(0_0_px2, 100_100_px2, Color.red)

    # World-space drawing (auto-converts via camera)
    with im.world_space(camera):
        circle(player.position, 1_m)  # 1 meter radius
```

### 12.7 Validation in Custom Types

Custom types can include validation in their `from_parts` implementation:

```simple
struct NormalizedVec3:
    x: f32
    y: f32
    z: f32

impl FromLiteral for NormalizedVec3:
    const SUFFIX = "norm3"
    const ARITY = 3

    fn from_parts(parts: [f32; 3]) -> Self:
        let len = sqrt(parts[0]*parts[0] + parts[1]*parts[1] + parts[2]*parts[2])
        if len < 0.0001:
            panic("Cannot normalize zero vector")
        NormalizedVec3(parts[0]/len, parts[1]/len, parts[2]/len)

# Usage - automatically normalized
direction = 1_1_0_norm3              # NormalizedVec3(0.707, 0.707, 0)
```

### 12.8 Compile-Time Validation

The compiler validates multi-value literals at compile time:

```
error: wrong number of values for `_vec3` literal
  --> example.spl:10:15
   |
10 | let v = 1_2_vec3
   |         ^^^^^^^^ expected 3 values, found 2
   |
   = help: `Vec3` requires exactly 3 values: x, y, z
   = hint: use `1_2_0_vec3` for a vector with z=0

error: unknown literal suffix `_foo`
  --> example.spl:15:15
   |
15 | let x = 1_2_3_foo
   |               ^^^ unknown suffix
   |
   = help: available suffixes: loc, loc3, vec2, vec3, rect, ...
   = hint: define a custom type with `impl FromLiteral`
```

---

## Related Specifications

- [Types](types.md)
- [Data Structures](data_structures.md)
- [Standard Library](stdlib.md)
- [Vulkan DSL Research](../research/vulkan_dsl.md) - Graphics DSL with multi-value literals
