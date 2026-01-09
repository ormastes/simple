# Simple Language Data Structures - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/data_structures_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/data_structures_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** data_structures.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from data_structures.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/data_structures.md

---

## Test Cases (32 total)

| Test | Section | Description |
|------|---------|-------------|
| [structs_value_types_1](#test-1) | Structs (Value Types) | Structs are value types (similar to structs in C or Rust). T... |
| [structs_value_types_2](#test-2) | Structs (Value Types) | Unless marked `mut`, a struct's fields cannot be changed aft... |
| [classes_reference_types_3](#test-3) | Classes (Reference Types) | Classes are reference types, allocated on the heap and manag... |
| [classes_reference_types_4](#test-4) | Classes (Reference Types) | By default, class instances are mutable. Use `immut` for imm... |
| [classes_reference_types_5](#test-5) | Classes (Reference Types) | - Mutable by default - Use `immut class` for immutable class... |
| [auto_forwarding_properties_getsetis_6](#test-6) | Auto-Forwarding Properties (get/set/is) | Simple provides automatic property forwarding for methods pr... |
| [auto_forwarding_properties_getsetis_7](#test-7) | Auto-Forwarding Properties (get/set/is) | If only `get_` is defined, the property is read-only from ou... |
| [auto_forwarding_properties_getsetis_8](#test-8) | Auto-Forwarding Properties (get/set/is) | If only `set_` is defined, the property is write-only from o... |
| [enums_algebraic_data_types_9](#test-9) | Enums (Algebraic Data Types) | Enums define a type that can be one of several variants, eac... |
| [handle](#test-10) | Enums (Algebraic Data Types) | Enums are typically used with pattern matching: |
| [enums_algebraic_data_types_11](#test-11) | Enums (Algebraic Data Types) | Enums can have methods added via impl blocks: |
| [enums_algebraic_data_types_12](#test-12) | Enums (Algebraic Data Types) | fn scale(self, factor: f64) -> Shape:... |
| [strong_enums_13](#test-13) | Strong Enums | The `#[strong]` attribute enforces exhaustive explicit match... |
| [strong_enums_14](#test-14) | Strong Enums | Strong enums prevent bugs when new variants are added: |
| [strong_enums_15](#test-15) | Strong Enums | Use `#[allow(wildcard_match)]` to allow wildcards in specifi... |
| [example](#test-16) | Union Types | Simple supports union types for cases where a variable might... |
| [option_type_17](#test-17) | Option Type | A common enum representing "something or nothing": |
| [option_type_18](#test-18) | Option Type | Important: Simple requires explicit `Option[T]` for nullable... |
| [visibility_and_access_19](#test-19) | Visibility and Access | By default, all struct and class fields are publicly readabl... |
| [result_type_20](#test-20) | Result Type | A common enum representing "success or error": |
| [read_config](#test-21) | Result Type | The `?` operator propagates errors automatically: |
| [result_type_22](#test-22) | Result Type | ```simple... |
| [result_type_23](#test-23) | Result Type | ```simple... |
| [bitfields_24](#test-24) | Bitfields | Bitfields allow compact representation of data at the bit le... |
| [bitfields_25](#test-25) | Bitfields | The backing type (`u8`, `u16`, `u32`, `u64`) determines the ... |
| [bitfields_26](#test-26) | Bitfields | Fields can span multiple bits: |
| [bitfields_27](#test-27) | Bitfields | \| Property \| Description \|... |
| [bitfields_28](#test-28) | Bitfields | Use `suffix:repr` for simple bit-width specification. In typ... |
| [bitfields_29](#test-29) | Bitfields | Use `where` for range inference, overflow behavior, and debu... |
| [bitfields_30](#test-30) | Bitfields | Unit-typed bitfield fields maintain full type safety: |
| [bitfields_31](#test-31) | Bitfields | let pos = Position(x: 100_cm, y: 200_cm)... |
| [bitfields_32](#test-32) | Bitfields | In debug builds, assignments to bit-limited fields are check... |

---

### Test 1: Structs (Value Types)

*Source line: ~7*

**Test name:** `structs_value_types_1`

**Description:**

Structs are value types (similar to structs in C or Rust). They are copied on assignment and passed ...

**Code:**

```simple
test "structs_value_types_1":
    struct Point:
        x: f64
        y: f64

    a = Point(x: 1, y: 2)
    b = a              # copies the values x=1, y=2 into b
    # a.x = 5          # Error: Point is immutable by default
    assert_compiles()
```

### Test 2: Structs (Value Types)

*Source line: ~21*

**Test name:** `structs_value_types_2`

**Description:**

Unless marked `mut`, a struct's fields cannot be changed after construction:

**Code:**

```simple
test "structs_value_types_2":
    mut struct Cursor:
        x: f64
        y: f64

    let c = Cursor(x: 0, y: 0)
    c.x = 10           # OK: Cursor is mutable
    assert_compiles()
```

### Test 3: Classes (Reference Types)

*Source line: ~7*

**Test name:** `classes_reference_types_3`

**Description:**

Classes are reference types, allocated on the heap and managed by the runtime (with garbage collecti...

**Code:**

```simple
test "classes_reference_types_3":
    class Person:
        name: String
        age: i32

        fn birthday():
            self.age = self.age + 1

    let p = Person(name: "Alice", age: 30)
    p.birthday()          # now age is 31
    assert_compiles()
```

### Test 4: Classes (Reference Types)

*Source line: ~23*

**Test name:** `classes_reference_types_4`

**Description:**

By default, class instances are mutable. Use `immut` for immutable classes:

**Code:**

```simple
test "classes_reference_types_4":
    immut class Color:
        red: u8
        green: u8
        blue: u8

    # Fields cannot be changed after construction
    assert_compiles()
```

### Test 5: Classes (Reference Types)

*Source line: ~42*

**Test name:** `classes_reference_types_5`

**Description:**

- Mutable by default - Use `immut class` for immutable classes
- Reference equality by default - Ove...

**Code:**

```simple
test "classes_reference_types_5":
    let p = Person(name: "Alice", age: 30)
    let q = p              # q and p refer to the same object
    q.age = 31             # p.age is also 31
    assert_compiles()
```

### Test 6: Auto-Forwarding Properties (get/set/is)

*Source line: ~7*

**Test name:** `auto_forwarding_properties_getsetis_6`

**Description:**

Simple provides automatic property forwarding for methods prefixed with `get_`, `set_`, or `is_`. Th...

**Code:**

```simple
test "auto_forwarding_properties_getsetis_6":
    class Person:
        # These methods auto-create private backing field '_name'
        fn get_name() -> str:
            return _name

        fn set_name(value: str):
            _name = value

        # 'is_' prefix for boolean properties
        fn is_active() -> bool:
            return _active

    let p = Person()
    p.set_name("Alice")      # Sets _name
    print p.get_name()       # Gets _name -> "Alice"
    assert_compiles()
```

### Test 7: Auto-Forwarding Properties (get/set/is)

*Source line: ~37*

**Test name:** `auto_forwarding_properties_getsetis_7`

**Description:**

If only `get_` is defined, the property is read-only from outside:

**Code:**

```simple
test "auto_forwarding_properties_getsetis_7":
    class Counter:
        fn get_count() -> i64:
            return _count

        fn increment():
            _count = _count + 1  # Internal modification OK

    let c = Counter()
    c.increment()
    print c.get_count()  # OK: 1
    # c.set_count(100)   # Error: no setter defined
    assert_compiles()
```

### Test 8: Auto-Forwarding Properties (get/set/is)

*Source line: ~55*

**Test name:** `auto_forwarding_properties_getsetis_8`

**Description:**

If only `set_` is defined, the property is write-only from outside:

**Code:**

```simple
test "auto_forwarding_properties_getsetis_8":
    class SecureData:
        fn set_password(value: str):
            _password = hash(value)

        fn verify(input: str) -> bool:
            return hash(input) == _password

    let s = SecureData()
    s.set_password("secret123")
    # print s.get_password()  # Error: no getter defined
    assert_compiles()
```

### Test 9: Enums (Algebraic Data Types)

*Source line: ~7*

**Test name:** `enums_algebraic_data_types_9`

**Description:**

Enums define a type that can be one of several variants, each possibly carrying data. They are algeb...

**Code:**

```simple
test "enums_algebraic_data_types_9":
    enum Result[T]:
        Ok(value: T)
        Err(error: String)
    assert_compiles()
```

### Test 10: Enums (Algebraic Data Types)

*Source line: ~19*

**Test name:** `handle`

**Description:**

Enums are typically used with pattern matching:

**Code:**

```simple
fn handle(result: Result[i64]):
    match result:
        case Ok(val):
            print "Success: {val}"
        case Err(msg):
            print "Error: {msg}"
```

### Test 11: Enums (Algebraic Data Types)

*Source line: ~39*

**Test name:** `enums_algebraic_data_types_11`

**Description:**

Enums can have methods added via impl blocks:

**Code:**

```simple
test "enums_algebraic_data_types_11":
    enum Shape:
        Circle(radius: f64)
        Rectangle(width: f64, height: f64)

    impl Shape:
        fn area(self) -> f64:
            match self:
                case Circle(r): return 3.14159 * r * r
                case Rectangle(w, h): return w * h

        fn scale(self, factor: f64) -> Shape:
            match self:
                case Circle(r): return Shape.Circle(radius: r * factor)
                case Rectangle(w, h): return Shape.Rectangle(width: w * factor, height: h * factor)

        # Associated function (no self)
        fn unit_circle() -> Shape:
            return Shape.Circle(radius: 1.0)

    # Usage
    let s = Shape.Circle(radius: 5.0)
    print s.area()           # 78.54
    let s2 = s.scale(2.0)    # Circle with radius 10.0
    assert_compiles()
```

### Test 12: Enums (Algebraic Data Types)

*Source line: ~67*

**Test name:** `enums_algebraic_data_types_12`

**Description:**

fn scale(self, factor: f64) -> Shape:
        match self:
            case Circle(r): return Shape.C...

**Code:**

```simple
test "enums_algebraic_data_types_12":
    trait Drawable:
        fn draw(self)

    impl Drawable for Shape:
        fn draw(self):
            match self:
                case Circle(r): draw_circle(r)
                case Rectangle(w, h): draw_rect(w, h)

    # Common traits can be derived
    #[derive(Eq, Clone, Debug)]
    enum Color:
        Red
        Green
        Blue
    assert_compiles()
```

### Test 13: Strong Enums

*Source line: ~7*

**Test name:** `strong_enums_13`

**Description:**

The `#[strong]` attribute enforces exhaustive explicit matching, disallowing wildcard `_` patterns.

**Code:**

```simple
test "strong_enums_13":
    #[strong]
    enum HttpStatus:
        Ok
        NotFound
        ServerError
        BadRequest
        Unauthorized

    fn handle_status(status: HttpStatus) -> str:
        match status:
            case Ok: "Success"
            case NotFound: "Not found"
            case ServerError: "Server error"
            case BadRequest: "Bad request"
            case Unauthorized: "Unauthorized"
            # No _ allowed - all cases must be explicit
    assert_compiles()
```

### Test 14: Strong Enums

*Source line: ~30*

**Test name:** `strong_enums_14`

**Description:**

Strong enums prevent bugs when new variants are added:

**Code:**

```simple
test "strong_enums_14":
    # Without #[strong] - wildcard hides missing cases
    enum Status:
        Active
        Inactive
        Pending      # Added later

    fn process(s: Status):
        match s:
            case Active: activate()
            case Inactive: deactivate()
            case _: pass     # Silently ignores Pending - BUG!

    # With #[strong] - compiler catches missing cases
    #[strong]
    enum Status:
        Active
        Inactive
        Pending

    fn process(s: Status):
        match s:
            case Active: activate()
            case Inactive: deactivate()
            # ERROR: missing case 'Pending', wildcards not allowed
    assert_compiles()
```

### Test 15: Strong Enums

*Source line: ~70*

**Test name:** `strong_enums_15`

**Description:**

Use `#[allow(wildcard_match)]` to allow wildcards in specific functions:

**Code:**

```simple
test "strong_enums_15":
    #[allow(wildcard_match)]
    fn handle_some(e: Event):
        match e:
            case Click: on_click()
            case _: pass     # OK with attribute
    assert_compiles()
```

### Test 16: Union Types

*Source line: ~7*

**Test name:** `example`

**Description:**

Simple supports union types for cases where a variable might hold one of multiple types.

**Code:**

```simple
fn example(x: i64 | str):
    match x:
        case i: i64:
            print "Integer: {i}"
        case s: String:
            print "String: {s}"
```

### Test 17: Option Type

*Source line: ~5*

**Test name:** `option_type_17`

**Description:**

A common enum representing "something or nothing":

**Code:**

```simple
test "option_type_17":
    enum Option[T]:
        Some(value: T)
        None

    fn find(id: UserId) -> Option[User]:
        match lookup(id):
            case found:
                return Some(found)
            case _:
                return None
    assert_compiles()
```

### Test 18: Option Type

*Source line: ~20*

**Test name:** `option_type_18`

**Description:**

Important: Simple requires explicit `Option[T]` for nullable values. Implicit `nil` is a compile err...

**Code:**

```simple
test "option_type_18":
    # ERROR: Implicit nullable return
    fn find_user(id: UserId) -> User:  # Compile error if function can return nil
        ...

    # CORRECT: Explicit Option
    fn find_user(id: UserId) -> Option[User]:
        ...
    assert_compiles()
```

### Test 19: Visibility and Access

*Source line: ~5*

**Test name:** `visibility_and_access_19`

**Description:**

By default, all struct and class fields are publicly readable but only modifiable according to mutab...

**Code:**

```simple
test "visibility_and_access_19":
    class User:
        pub id: UserId           # Public field - uses semantic type
        pub name: str            # OK: str is allowed in public APIs
        pub status: UserStatus   # Uses enum instead of bool
        private password: str    # Private field

        fn verify(input: str) -> bool:   # OK: bool in private method
            return hash(input) == self.password
    assert_compiles()
```

### Test 20: Result Type

*Source line: ~5*

**Test name:** `result_type_20`

**Description:**

A common enum representing "success or error":

**Code:**

```simple
test "result_type_20":
    enum Result[T, E]:
        Ok(value: T)
        Err(error: E)

    fn parse_int(s: str) -> Result[i64, ParseError]:
        if s.is_numeric():
            return Ok(s.to_int())
        return Err(ParseError(msg: "Invalid number: {s}"))
    assert_compiles()
```

### Test 21: Result Type

*Source line: ~20*

**Test name:** `read_config`

**Description:**

The `?` operator propagates errors automatically:

**Code:**

```simple
fn read_config() -> Result[Config, IoError]:
    let content = read_file("config.toml")?  # Returns early if Err
    let parsed = parse_toml(content)?        # Returns early if Err
    return Ok(Config(parsed))

# Equivalent to:
fn read_config_verbose() -> Result[Config, IoError]:
    match read_file("config.toml"):
        case Ok(content):
            match parse_toml(content):
                case Ok(parsed): return Ok(Config(parsed))
                case Err(e): return Err(e)
        case Err(e): return Err(e)
```

### Test 22: Result Type

*Source line: ~38*

**Test name:** `result_type_22`

**Description:**

```simple
fn read_config() -> Result[Config, IoError]:
    let content = read_file("config.toml")?  ...

**Code:**

```simple
test "result_type_22":
    impl Result[T, E]:
        fn is_ok() -> bool
        fn is_err() -> bool
        fn unwrap() -> T                    # Panics if Err
        fn unwrap_or(default: T) -> T
        fn unwrap_err() -> E                # Panics if Ok
        fn map[U](f: fn(T) -> U) -> Result[U, E]
        fn map_err[F](f: fn(E) -> F) -> Result[T, F]
        fn and_then[U](f: fn(T) -> Result[U, E]) -> Result[U, E]
    assert_compiles()
```

### Test 23: Result Type

*Source line: ~52*

**Test name:** `result_type_23`

**Description:**

```simple
impl Result[T, E]:
    fn is_ok() -> bool
    fn is_err() -> bool
    fn unwrap() -> T    ...

**Code:**

```simple
test "result_type_23":
    # These are equivalent:
    fn foo() -> Result[i64, Error]
    fn foo() -> i64 | Error
    assert_compiles()
```

### Test 24: Bitfields

*Source line: ~7*

**Test name:** `bitfields_24`

**Description:**

Bitfields allow compact representation of data at the bit level, useful for hardware registers, prot...

**Code:**

```simple
test "bitfields_24":
    bitfield Flags(u8):
        readable: 1      # bit 0
        writable: 1      # bit 1
        executable: 1    # bit 2
        _reserved: 5     # bits 3-7 (padding, not accessible)
    assert_compiles()
```

### Test 25: Bitfields

*Source line: ~19*

**Test name:** `bitfields_25`

**Description:**

The backing type (`u8`, `u16`, `u32`, `u64`) determines the total size.

**Code:**

```simple
test "bitfields_25":
    let f = Flags(readable: 1, writable: 1, executable: 0)
    print f.readable     # 1
    f.writable = 0       # Clear write bit
    let raw = f.raw()    # Get underlying u8 value: 0b00000001
    assert_compiles()
```

### Test 26: Bitfields

*Source line: ~30*

**Test name:** `bitfields_26`

**Description:**

Fields can span multiple bits:

**Code:**

```simple
test "bitfields_26":
    bitfield Color(u32):
        red: 8           # bits 0-7
        green: 8         # bits 8-15
        blue: 8          # bits 16-23
        alpha: 8         # bits 24-31

    let c = Color(red: 255, green: 128, blue: 64, alpha: 255)
    assert_compiles()
```

### Test 27: Bitfields

*Source line: ~51*

**Test name:** `bitfields_27`

**Description:**

| Property | Description |
|----------|-------------|
| Packed | Fields are tightly packed with no p...

**Code:**

```simple
test "bitfields_27":
    bitfield Permission(u8):
        read: 1
        write: 1
        execute: 1

        const READ_ONLY = Permission(read: 1, write: 0, execute: 0)
        const READ_WRITE = Permission(read: 1, write: 1, execute: 0)
        const FULL = Permission(read: 1, write: 1, execute: 1)
    assert_compiles()
```

### Test 28: Bitfields

*Source line: ~70*

**Test name:** `bitfields_28`

**Description:**

Use `suffix:repr` for simple bit-width specification. In type positions, use bare unit suffix (no un...

**Code:**

```simple
test "bitfields_28":
    bitfield RobotArm:
        x: cm:i12           # 12-bit signed centimeters
        y: cm:i12           # 12-bit signed centimeters
        z: cm:u10           # 10-bit unsigned centimeters
        angle: deg:u9       # 9-bit unsigned degrees (0-511)
        grip: pct:u7        # 7-bit percentage (0-100)

    # Literals still use underscore prefix
    let arm = RobotArm(x: 100_cm, y: -50_cm, z: 200_cm, angle: 180_deg, grip: 75_pct)
    print arm.x              # 100_cm (typed value, not raw bits)
    print arm.angle          # 180_deg
    assert_compiles()
```

### Test 29: Bitfields

*Source line: ~88*

**Test name:** `bitfields_29`

**Description:**

Use `where` for range inference, overflow behavior, and debug checking:

**Code:**

```simple
test "bitfields_29":
    bitfield SensorData:
        # Range inference - compiler calculates minimum bits
        temp: celsius where range: -40..125            # infers i8
        humidity: pct where range: 0..100              # infers u7

        # Explicit repr + overflow behavior
        pressure: hpa:u16 where checked                # panic on overflow
        altitude: m:i16 where saturate                 # clamp to min/max
        heading: deg:u9 where wrap                     # modular arithmetic (0-511)

    bitfield MotorControl:
        # Combined constraints
        position: cm where range: -1000..1000, checked     # i11, debug-checked
        velocity: mps:u8 where saturate                    # clamp to 0-255
        torque: nm where range: 0..100, default: 0_nm      # with default value
    assert_compiles()
```

### Test 30: Bitfields

*Source line: ~146*

**Test name:** `bitfields_30`

**Description:**

Unit-typed bitfield fields maintain full type safety:

**Code:**

```simple
test "bitfields_30":
    bitfield Position:
        x: cm:i12
        y: cm:i12

    let pos = Position(x: 100_cm, y: 200_cm)
    # pos.x = 50_m      # ERROR: cannot assign m to cm field
    # pos.x = 50        # ERROR: cannot assign bare integer to cm field
    pos.x = 50_cm       # OK: same unit type

    # Arithmetic preserves unit type
    let new_x = pos.x + 10_cm    # Result: cm:i12
    assert_compiles()
```

### Test 31: Bitfields

*Source line: ~162*

**Test name:** `bitfields_31`

**Description:**

let pos = Position(x: 100_cm, y: 200_cm)
# pos.x = 50_m      # ERROR: cannot assign m to cm field
# ...

**Code:**

```simple
test "bitfields_31":
    bitfield Compact:
        dist: cm:u8

    bitfield Wide:
        dist: cm:u16

    let c = Compact(dist: 100_cm)
    let w = Wide(dist: c.dist.widen())    # Explicit widening
    # let w2 = Wide(dist: c.dist)         # OK: implicit widening allowed

    let c2 = Compact(dist: w.dist.narrow())   # Explicit narrowing (checked)
    let c3 = Compact(dist: w.dist.saturate()) # Clamp to 0-255
    assert_compiles()
```

### Test 32: Bitfields

*Source line: ~181*

**Test name:** `bitfields_32`

**Description:**

In debug builds, assignments to bit-limited fields are checked:

**Code:**

```simple
test "bitfields_32":
    bitfield Test:
        value: cm:u8              # 0-255 range

    let t = Test(value: 255_cm)   # OK
    # t.value = 256_cm            # Debug: panic! Release: undefined behavior

    bitfield SafeTest:
        value: cm:u8 where checked    # Always checked

    let s = SafeTest(value: 255_cm)
    # s.value = 256_cm            # Always panic (debug and release)

    bitfield ClampTest:
        value: cm:u8 where saturate

    let cl = ClampTest(value: 300_cm)
    print cl.value                # 255_cm (clamped)
    assert_compiles()
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/data_structures_spec.spl`*
