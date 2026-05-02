# Simple Language Unit Types Specification

This document specifies the unit type system and the requirement to use semantic types instead of bare primitives.

## Design Philosophy

Simple encourages **semantic typing** - using meaningful types instead of bare primitives. This prevents bugs like:
- Mixing up user IDs and order IDs (both `i64`)
- Confusing meters and feet (both `f64`)
- Passing raw booleans where domain-specific flags are expected

**Core Principle**: Bare primitive types (`i32`, `i64`, `f64`, `bool`, etc.) should NOT appear in public APIs. Use unit types, newtypes, enums, or Option types instead.

**Enforcement**: The compiler emits warnings for bare primitives in public APIs. Projects can upgrade warnings to errors using `#![deny(primitive_api)]`. The standard library uses this attribute to ensure zero primitive API warnings.

---

## 1. Primitive Type Warnings

### 1.1 Public API Rules

**WARNING** in public APIs (can be upgraded to error with `#[deny(primitive_api)]`):
- Bare numeric types: `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64`
- Bare `bool` (use enums or semantic booleans)

**WARNING** in public APIs (can be upgraded to error with `#[deny(bare_string)]`):
- Bare `str` or `String` - use semantic string unit types (e.g., `FilePath`, `Url`, `IpAddr`)

**ERROR** (always, cannot be suppressed):
- Implicit `nil` without `Option[T]` - must use `Option[T]` explicitly

**NO WARNING** in public APIs:
- String unit types (e.g., `FilePath`, `Url`, `IpAddr`, `Host`)
- Numeric unit types (e.g., `UserId`, `Meters`, `Seconds`, `Port`)
- Newtypes wrapping primitives
- Enums for states and flags
- `Option[T]` for nullable values
- `Result[T, E]` for fallible operations

### 1.2 Compiler Enforcement

```simple
# WARNING: Bare primitive in public function
pub fn get_user_id() -> i64:        # Warning: use unit type
    return 42

# OK: Unit type (no warning)
pub fn get_user_id() -> UserId:
    return 42_uid

# WARNING: Bare bool parameter
pub fn set_active(active: bool):    # Warning: use enum
    ...

# OK: Semantic enum (no warning)
pub fn set_status(status: UserStatus):
    ...

# WARNING: Bare string in public function
pub fn read_file(path: str) -> Bytes:    # Warning: use FilePath
    ...

# OK: String unit type (no warning)
pub fn read_file(path: FilePath) -> Bytes:
    ...

# WARNING: Bare string return type
pub fn get_server_address() -> str:      # Warning: use IpAddr or Url
    ...

# OK: Semantic string type (no warning)
pub fn get_server_address() -> IpAddr:
    ...

# ERROR: Nullable without Option (always an error)
pub fn find_user(id: UserId) -> User:  # Compile ERROR if can return nil
    ...

# OK: Explicit Option
pub fn find_user(id: UserId) -> Option[User]:
    ...
```

### 1.3 Private Code Allowance

Private/internal code MAY use bare primitives for implementation convenience:

```simple
# OK in private scope
fn internal_compute(a: i64, b: i64) -> i64:
    return a + b

# Public wrapper must use semantic types
pub fn compute_distance(from: Position, to: Position) -> Distance:
    let dx = internal_compute(from.x.raw(), to.x.raw())
    let dy = internal_compute(from.y.raw(), to.y.raw())
    return Distance.from_raw(sqrt(dx*dx + dy*dy))
```

### 1.4 Explicit Override

Use `#[allow(primitive_api)]` only for legitimate low-level cases:

```simple
# Low-level byte manipulation
#[allow(primitive_api)]
pub fn read_bytes(count: i32) -> [u8]:
    ...

# FFI boundaries
#[allow(primitive_api)]
pub extern fn c_function(ptr: *u8, len: i32) -> i32:
    ...
```

This attribute should be rare - most code should use semantic types.

---

## 2. Unit Type Definitions

### 2.1 Basic Unit Types (Newtypes)

```simple
# Syntax: unit Name: BaseType as suffix
unit UserId: i64 as uid
unit OrderId: i64 as oid
unit ProductId: i64 as pid

# Usage
let user = 42_uid           # UserId
let order = 100_oid         # OrderId

# Type safety - compile error:
# let bad: UserId = 100_oid  # Error: OrderId ≠ UserId
```

### 2.2 Multi-Base Unit Types

Some unit types accept multiple literal forms (e.g., IP addresses as string or integer):

```simple
# Syntax: unit Name: Type1 | Type2 as suffix
unit IpAddr: str | u32 as ip
unit MacAddr: str | u64 as mac

# Usage - both forms create the same type
let ip_str = "127.0.0.1"_ip      # From string literal
let ip_num = 0x7F000001_ip       # From numeric literal (hex)
let ip_dec = 2130706433_ip       # From numeric literal (decimal)

# All three are equivalent IpAddr values
assert ip_str == ip_num          # true
assert ip_num == ip_dec          # true
```

**How multi-base works:**
- The compiler detects the literal type (string vs numeric)
- String literals call `Type::from_str(value)`
- Numeric literals call `Type::from_<base_type>(value)` (e.g., `from_u32`)
- Both produce the same result type

**Implementation requirement:**
```simple
impl IpAddr:
    fn from_str(s: str) -> Result[IpAddr, AddrError]
    fn from_u32(n: u32) -> IpAddr    # For numeric literals
```

### 2.3 Physical Unit Families

```simple
# Syntax: unit family_name(base: BaseType): suffix = factor, ...
unit length(base: f64):
    mm = 0.001
    cm = 0.01
    m = 1.0               # base unit
    km = 1000.0
    inch = 0.0254
    ft = 0.3048
    mile = 1609.34

unit time(base: f64):
    ns = 0.000000001
    us = 0.000001
    ms = 0.001
    s = 1.0               # base unit
    min = 60.0
    hr = 3600.0
    day = 86400.0

unit mass(base: f64):
    mg = 0.000001
    g = 0.001
    kg = 1.0              # base unit
    lb = 0.453592
    oz = 0.0283495

unit temperature(base: f64):
    K = 1.0               # Kelvin as base
    # Celsius and Fahrenheit need conversion functions
```

### 2.4 Composite Units

```simple
# Syntax: unit name(base: BaseType) = family1 op family2: ...
unit velocity(base: f64) = length / time:
    mps = 1.0             # meters per second
    kmph = 0.277778       # km/hr in m/s
    mph = 0.44704         # miles/hr in m/s
    knot = 0.514444

unit area(base: f64) = length * length:
    sqmm = 0.000001
    sqcm = 0.0001
    sqm = 1.0
    sqkm = 1000000.0
    acre = 4046.86
    hectare = 10000.0

unit volume(base: f64) = length * length * length:
    ml = 0.000001
    L = 0.001
    m3 = 1.0
    gal = 0.00378541

unit acceleration(base: f64) = velocity / time:
    mps2 = 1.0            # m/s²
    g = 9.80665           # standard gravity

unit force(base: f64) = mass * acceleration:
    N = 1.0               # Newton
    kN = 1000.0
    lbf = 4.44822

unit energy(base: f64) = force * length:
    J = 1.0               # Joule
    kJ = 1000.0
    cal = 4.184
    kcal = 4184.0
    kWh = 3600000.0

unit power(base: f64) = energy / time:
    W = 1.0               # Watt
    kW = 1000.0
    MW = 1000000.0
    hp = 745.7
```

### 2.5 Percentage and Ratio Units

```simple
unit Percentage: f64 as pct = 0.01
unit Ratio: f64 as ratio

# Usage
let discount = 20_pct         # stored as 0.2
let tax_rate = 8.5_pct        # stored as 0.085
let scale = 1.5_ratio

let price = 100.0
let final_price = price * (1.0 - discount.value())  # 80.0
```

### 2.6 Currency Units

```simple
unit currency(base: i64):     # Use i64 for precision (cents/pence)
    usd_cent = 1
    usd = 100
    eur_cent = 1
    eur = 100
    gbp_penny = 1
    gbp = 100
    jpy = 1               # Yen has no subunit

# Usage
let price = 1999_usd_cent     # $19.99
let total = 50_usd            # $50.00
```

---

## 3. Semantic Boolean Types

### 3.1 Replace bool with Enums

**Instead of bare `bool`**, use descriptive enums:

```simple
# BAD: What does true/false mean?
fn set_user(active: bool, verified: bool, admin: bool):
    ...

# GOOD: Clear meaning
enum UserStatus:
    Active
    Inactive
    Suspended

enum VerificationState:
    Verified
    Unverified
    Pending

enum Role:
    User
    Moderator
    Admin

fn configure_user(status: UserStatus, verification: VerificationState, role: Role):
    ...
```

### 3.2 Standard Boolean Enums

The stdlib provides common semantic boolean types:

```simple
# std.types.flags

enum Enabled:
    Yes
    No

enum Visibility:
    Visible
    Hidden

enum Required:
    Required
    Optional

enum ReadOnly:
    ReadOnly
    ReadWrite

enum Sorted:
    Sorted
    Unsorted

enum Nullable:
    Nullable
    NonNull
```

### 3.3 Flag Sets

For multiple boolean-like options, use flag enums:

```simple
#[flags]
enum FilePermissions:
    Read = 1
    Write = 2
    Execute = 4

# Usage
let perms = FilePermissions.Read | FilePermissions.Write
if perms.has(FilePermissions.Read):
    ...
```

---

## 4. Option and Result Types

### 4.1 No Bare nil

**FORBIDDEN**: Returning or passing `nil` without `Option`:

```simple
# ERROR: Implicit nullable
fn find(id: UserId) -> User:
    if exists(id):
        return load(id)
    return nil              # Compile error!

# OK: Explicit Option
fn find(id: UserId) -> Option[User]:
    if exists(id):
        return Some(load(id))
    return None
```

### 4.2 Option Type

```simple
enum Option[T]:
    Some(value: T)
    None

# Methods
impl Option[T]:
    fn is_some(self) -> bool
    fn is_none(self) -> bool
    fn unwrap(self) -> T              # Panics if None
    fn unwrap_or(self, default: T) -> T
    fn map[U](self, f: fn(T) -> U) -> Option[U]
    fn and_then[U](self, f: fn(T) -> Option[U]) -> Option[U]
    fn or_else(self, f: fn() -> Option[T]) -> Option[T]
```

### 4.3 Result Type

```simple
enum Result[T, E]:
    Ok(value: T)
    Err(error: E)

# Methods
impl Result[T, E]:
    fn is_ok(self) -> bool
    fn is_err(self) -> bool
    fn unwrap(self) -> T              # Panics if Err
    fn unwrap_err(self) -> E          # Panics if Ok
    fn map[U](self, f: fn(T) -> U) -> Result[U, E]
    fn map_err[F](self, f: fn(E) -> F) -> Result[T, F]
    fn and_then[U](self, f: fn(T) -> Result[U, E]) -> Result[U, E]
```

### 4.4 The `?` Operator

```simple
fn process(id: UserId) -> Result[Report, Error]:
    let user = find_user(id)?         # Returns Err if None/Err
    let data = load_data(user)?
    let report = generate(data)?
    return Ok(report)
```

---

## 5. Standard Library Unit Modules

### 5.1 Module Structure

```
std/
  units/
    core.spl           # Unit type infrastructure
    ids.spl            # ID types (UserId, etc.)
    physical/
      length.spl
      time.spl
      mass.spl
      temperature.spl
      derived.spl      # velocity, acceleration, force, etc.
    money/
      currency.spl
    ratios.spl         # Percentage, Ratio
  types/
    flags.spl          # Semantic boolean enums
    option.spl
    result.spl
```

### 5.2 std.units.core

```simple
# Base traits for unit types

trait Unit:
    type Base           # Underlying primitive type
    fn raw(self) -> Self.Base
    fn from_raw(value: Self.Base) -> Self

trait UnitFamily:
    type Base
    fn to_base(self) -> Self.Base
    fn from_base(value: Self.Base) -> Self

trait Convertible[To]:
    fn convert(self) -> To
```

### 5.3 std.units.ids

```simple
# Common ID types

unit UserId: i64 as uid
unit SessionId: i64 as sid
unit RequestId: i64 as rid
unit TransactionId: i64 as tid

# UUID-based IDs
unit Uuid: [u8; 16] as uuid

# String-based IDs
unit Slug: str as slug
unit Email: str as email     # With validation
```

### 5.4 std.units.file - File System Units

```simple
# File path unit - supports mingw-style drive letters
unit FilePath: str as file

# File path components
unit FileName: str as filename
unit FileExt: str as ext
unit DirPath: str as dir
unit DriveLetter: str as drive    # Windows only: "C", "D", etc.

# Usage
let config = "/etc/config.json"_file
let win_path = "C:/Users/data.txt"_file    # mingw-style
let name = "readme"_filename
let ext = "md"_ext
```

**FilePath API:**
```simple
impl FilePath:
    fn dir(self) -> Option[DirPath]
    fn file_name(self) -> Option[FileName]
    fn extension(self) -> Option[FileExt]
    fn drive(self) -> Option[DriveLetter]   # Windows/mingw only
    fn join(self, child: FilePath) -> FilePath
    fn parent(self) -> Option[FilePath]
    fn to_native(self) -> str               # Platform-native separators
    fn to_posix(self) -> str                # Forward slashes
    fn to_mingw(self) -> str                # C:/path/to/file
    fn is_absolute(self) -> bool
```

### 5.5 std.units.net - Network Units

Network units support **multi-base definitions** - accepting both string and numeric literals:

```simple
# IP addresses - multi-base unit (str or u32)
unit IpAddr: str | u32 as ip
unit Ipv4Addr: str | u32 as ipv4
unit Ipv6Addr: str | u128 as ipv6

# Port number
unit Port: u16 as port

# Socket address (IP + port)
unit SocketAddr: str as sock

# MAC address - multi-base (str or u64)
unit MacAddr: str | u64 as mac

# Usage - String format (human-readable)
let localhost = "127.0.0.1"_ip
let v6 = "::1"_ipv6
let port = 8080_port
let endpoint = "127.0.0.1:8080"_sock
let mac = "00:1A:2B:3C:4D:5E"_mac

# Usage - Numeric format (efficient, no parsing)
let localhost_num = 0x7F000001_ip      # 127.0.0.1 as u32
let broadcast = 0xFFFFFFFF_ip          # 255.255.255.255
let mac_num = 0x001A2B3C4D5E_mac       # MAC as 48-bit integer
```

**Multi-base unit semantics:**

The syntax `unit IpAddr: str | u32 as ip` means:
- `"127.0.0.1"_ip` → calls `IpAddr::from_str("127.0.0.1")`
- `0x7F000001_ip` → calls `IpAddr::from_u32(0x7F000001)`
- Both produce the same `IpAddr` type

**IpAddr API:**
```simple
impl IpAddr:
    fn v4(a: u8, b: u8, c: u8, d: u8) -> Ipv4Addr
    fn from_str(s: str) -> Result[IpAddr, AddrError]
    fn from_u32(n: u32) -> Ipv4Addr         # For numeric literals
    fn localhost() -> IpAddr
    fn any() -> IpAddr                      # 0.0.0.0
    fn is_v4(self) -> bool
    fn is_v6(self) -> bool
    fn is_loopback(self) -> bool
    fn is_private(self) -> bool
    fn to_u32(self) -> Option[u32]          # Only for IPv4
    fn to_str(self) -> str
```

### 5.6 std.units.url - URL Units

```simple
# Generic URL
unit Url: str as url

# Protocol-specific URLs
unit HttpUrl: str as http       # http:// or https://
unit FtpUrl: str as ftp         # ftp://
unit FileUrl: str as fileurl    # file://

# URL components
unit Scheme: str as scheme
unit Host: str as host
unit UrlPath: str as urlpath
unit Query: str as query
unit Fragment: str as fragment

# HTTP-specific
unit StatusCode: u16 as status
unit HeaderName: str as header
unit HeaderValue: str as hval

# Usage
let api = "https://api.example.com/v1"_http
let ftp_server = "ftp://files.example.com"_ftp
let status = 200_status
let content_type = "Content-Type"_header
```

**Url API:**
```simple
impl Url:
    fn scheme(self) -> Scheme
    fn host(self) -> Option[Host]
    fn port(self) -> Option[Port]
    fn path(self) -> UrlPath
    fn query(self) -> Option[Query]
    fn join(self, path: UrlPath) -> Url
```

### 5.7 std.units.size - Data Size Units

```simple
unit size(base: u64):
    byte = 1
    kb = 1024
    mb = 1048576
    gb = 1073741824
    tb = 1099511627776

# Shorthand aliases
unit ByteCount: u64 as bytes

# Usage
let file_size = 1024_bytes
let memory = 512_mb
let disk = 2_tb
```

### 5.8 Creating Custom Unit Types

```simple
use std.units.core.Unit

# Define your domain-specific units
unit CustomerId: i64 as cid

impl Unit for CustomerId:
    type Base = i64

    fn raw(self) -> i64:
        return self.0

    fn from_raw(value: i64) -> CustomerId:
        return CustomerId(value)

# With validation
unit PositiveInt: i64 as pos

impl PositiveInt:
    fn new(value: i64) -> Result[PositiveInt, ValueError]:
        if value <= 0:
            return Err(ValueError("must be positive"))
        return Ok(PositiveInt(value))

    fn raw(self) -> i64:
        return self.0
```

---

## 6. Type Conversion and Operations

### 6.1 Automatic Unit Conversion

Within the same unit family, conversions are automatic:

```simple
let d1 = 1_km
let d2 = 500_m

let total = d1 + d2           # OK: both length, result in base unit (meters)
print total.as_km()           # 1.5
print total.as_m()            # 1500.0
```

### 6.2 Composite Type Inference

```simple
let distance = 100_km
let time = 2_hr

# Compiler infers: length / time = velocity
let speed = distance / time   # velocity type

print speed.as_kmph()         # 50.0
print speed.as_mph()          # 31.07...
```

### 6.3 Explicit Conversion

```simple
# Between incompatible types - explicit conversion required
let meters = 100_m
let feet = meters.to(ft)      # Explicit conversion

# Or using conversion factor
let feet = Feet.from_meters(meters)
```

### 6.4 Arithmetic Rules

| Operation | Left Type | Right Type | Result Type |
|-----------|-----------|------------|-------------|
| `+`, `-` | `length` | `length` | `length` |
| `*` | `length` | `length` | `area` |
| `*` | `length` | `scalar` | `length` |
| `/` | `length` | `time` | `velocity` |
| `/` | `length` | `length` | `scalar` (ratio) |

---

## 7. Type-Safe Unit Arithmetic

### 7.1 Overview

Simple supports **type-safe unit arithmetic** - operations that prevent invalid combinations like adding kilometers to hours. Unit families can declare allowed operations, compound units enable derived types like velocity, and custom functions support domain-specific operations.

**Design Principles:**
- **Default deny**: No arithmetic allowed unless explicitly declared
- **Compile-time safety**: Invalid operations fail at compile time
- **Extensibility**: Custom operations (log, exp, sqrt) for domain needs

### 7.2 Arithmetic Rules Grammar

Unit families can declare arithmetic rules in an optional block:

```ebnf
unit_family_def = "unit" IDENT "(" "base" ":" type ")" ":" variant_list [ ":" NEWLINE INDENT arithmetic_block DEDENT ]

variant_list = variant ("," variant)*
variant = IDENT "=" NUMBER

arithmetic_block = arithmetic_rule+
arithmetic_rule = binary_rule | unary_rule | custom_fn

binary_rule = "allow" binary_op "(" type_param ")" "->" type_result
unary_rule = "allow" unary_op "->" type_result
custom_fn = "fn" IDENT "(" params ")" [ "->" type ] ":" NEWLINE INDENT body DEDENT

binary_op = "add" | "sub" | "mul" | "div" | "mod"
unary_op = "neg" | "abs"
```

### 7.3 Unit Family with Arithmetic Rules

```simple
unit length(base: f64): m = 1.0, km = 1000.0, cm = 0.01:
    # Type-safe: length + length -> length
    allow add(length) -> length
    allow sub(length) -> length

    # Scaling: length * number -> length
    allow mul(f64) -> length
    allow div(f64) -> length

    # Unary operations
    allow neg -> length
    allow abs -> length

    # Custom operations (return raw value, loses unit)
    fn log(self) -> f64:
        return log(self.value())

    fn exp(self) -> f64:
        return exp(self.value())

    fn sqrt(self) -> f64:
        return sqrt(self.value())
```

### 7.4 Default Arithmetic Behavior

If a unit family has **no arithmetic block**, no arithmetic is allowed:

```simple
unit user_id(base: u64): uid = 1
# user_id + user_id -> ERROR (no rules defined)

let a = 1_uid
let b = 2_uid
let c = a + b    # Compile error: arithmetic not allowed for user_id
```

This prevents accidental operations on ID types, counters, or other semantic units where arithmetic is meaningless.

---

**Continued in:** [Part 2](./units_part2.md)
