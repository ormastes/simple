# Const Functions and Compile-Time Evaluation: Configuration Design

**Date**: 2026-02-05
**Status**: Design
**Related**: `doc/design/baremetal_features_examples.md`, `doc/research/const_contract_partial_const_2026-01-21.md`

---

## Overview

Compile-time evaluation enables:
1. **Const functions** - Functions that can execute at compile time
2. **Comptime blocks** - Code that must execute at compile time
3. **Const values** - Values computed at compile time
4. **Static assertions** - Compile-time verification

---

## Configuration Levels (Priority: High to Low)

| Level | Scope | Syntax | Use Case |
|-------|-------|--------|----------|
| **Expression** | Single value | `const x = expr` | Const variable |
| **Function** | Single function | `const fn` | Const function |
| **Block** | Code block | `comptime { }` | Forced compile-time |
| **Module** | All functions in file | `__init__: comptime_*` | Module settings |
| **Project** | All files | `simple.sdn [comptime]` | Project defaults |

---

## Level 1: Expression-Level Const

### Const Variables

```simple
# Const value - must be computable at compile time
const PI: f64 = 3.14159265358979
const TAU: f64 = PI * 2.0
const BUFFER_SIZE: i32 = 1024
const MAX_CONNECTIONS: i32 = BUFFER_SIZE / 16

# Const from const fn
const CRC_TABLE: [u32; 256] = generate_crc_table()
const LOOKUP: [i32; 100] = generate_lookup()

# Const in type position
struct Buffer:
    data: [u8; BUFFER_SIZE]    # Size from const

# Const in array initializer
val zeros: [u8; BUFFER_SIZE] = [0; BUFFER_SIZE]
```

### Const Expressions

```simple
# Arithmetic
const A = 1 + 2 * 3           # 7
const B = (100 - 50) / 2      # 25

# Bitwise
const FLAGS = 0x01 | 0x02 | 0x04   # 0x07
const MASK = ~0xFF            # Inverted

# Comparison (becomes const bool)
const IS_64BIT = size_of<usize>() == 8
const HAS_FPU = cfg("target_has_fpu")

# Conditional const
const DEFAULT_STACK = if IS_64BIT: 16384 else: 8192

# String const
const VERSION = "1.0.0"
const APP_NAME = "MyApp"
const FULL_NAME = APP_NAME + " v" + VERSION
```

---

## Level 2: Function-Level Const

### Const Function Definition

```simple
# Basic const fn
const fn square(x: i32) -> i32:
    x * x

# Const fn with control flow
const fn factorial(n: i32) -> i32:
    if n <= 1: 1
    else: n * factorial(n - 1)

# Const fn with loops
const fn sum_to(n: i32) -> i32:
    var total = 0
    for i in 0..=n:
        total += i
    total

# Const fn returning array
const fn generate_squares(n: i32) -> [i32; n]:
    var result = [0; n]
    for i in 0..n:
        result[i] = i * i
    result

# Usage
const FACT_10: i32 = factorial(10)       # Computed at compile time
const SQUARES: [i32; 10] = generate_squares(10)
```

### Const Fn Restrictions

```simple
const fn allowed_operations(x: i32) -> i32:
    # Allowed:
    val a = x + 1           # Arithmetic
    val b = if a > 0: a else: -a  # Conditionals
    var c = 0               # Local variables
    for i in 0..10:         # Loops with const bounds
        c += i
    c                       # Return

const fn not_allowed():
    # NOT allowed in const fn:
    # - I/O operations (print, file access)
    # - Heap allocation (Vec::new, Box::new)
    # - Runtime-only functions
    # - Panic (unless comptime_panic enabled)
    # - Unbounded recursion
    # - Floating point (unless comptime_float enabled)
    pass
```

### Const Fn with Generic Types

```simple
const fn array_sum<T: Add + Zero, const N: i32>(arr: [T; N]) -> T:
    var sum = T.zero()
    for i in 0..N:
        sum = sum + arr[i]
    sum

const fn array_map<T, U, const N: i32>(arr: [T; N], f: const fn(T) -> U) -> [U; N]:
    var result: [U; N]
    for i in 0..N:
        result[i] = f(arr[i])
    result

# Usage
const NUMBERS: [i32; 5] = [1, 2, 3, 4, 5]
const SUM: i32 = array_sum(NUMBERS)           # 15
const DOUBLED: [i32; 5] = array_map(NUMBERS, |x| x * 2)  # [2,4,6,8,10]
```

---

## Level 3: Block-Level Comptime

### Comptime Block

```simple
# Force compile-time evaluation
comptime:
    val TABLE = generate_large_table()
    val CHECKSUM = compute_checksum(TABLE)

# Comptime with assertions
comptime:
    val size = compute_buffer_size()
    static assert size <= 4096, "Buffer too large"
    static assert size % 64 == 0, "Buffer must be 64-byte aligned"

# Comptime conditional compilation
comptime:
    if cfg("target") == "embedded":
        const STACK_SIZE = 2048
    else:
        const STACK_SIZE = 16384
```

### Comptime Loops (Unrolling)

```simple
# Generate code at compile time
fn process_channels():
    comptime for i in 0..8:
        # This generates 8 separate function calls
        process_channel_{i}()

# Comptime match
fn select_algorithm<const MODE: i32>():
    comptime match MODE:
        0: fast_algorithm()
        1: accurate_algorithm()
        2: balanced_algorithm()
        _: static assert false, "Invalid mode"
```

### Comptime Type Computation

```simple
# Compute type at compile time
comptime:
    type BufferType = if cfg("large_memory"):
        [u8; 65536]
    else:
        [u8; 1024]

struct Config:
    buffer: BufferType

# Comptime type selection
const fn select_int_type(bits: i32) -> type:
    if bits <= 8: u8
    elif bits <= 16: u16
    elif bits <= 32: u32
    else: u64

type SmallInt = select_int_type(12)   # u16
```

---

## Level 4: Module-Level Configuration (`__init__`)

### Default Comptime Settings

```simple
# src/lib/tables/__init__.spl
__init__:
    # All functions in this module are const by default
    comptime_default = true

    # Allow floating point in const fn
    comptime_float = true

    # Allow panic in const fn (becomes compile error)
    comptime_panic = true

    # Maximum recursion depth for const fn
    comptime_max_recursion = 1000

    # Maximum iterations for const loops
    comptime_max_iterations = 100000

    # Maximum memory for const evaluation
    comptime_max_memory = "16M"

# Functions are const by default
fn generate_sin_table() -> [f64; 360]:    # Implicitly const
    var table: [f64; 360]
    for i in 0..360:
        table[i] = sin(i as f64 * PI / 180.0)
    table

# Explicitly not const
runtime fn read_calibration() -> [f64; 360]:
    # This function cannot be called at compile time
    file_read("calibration.dat")
```

### Const Evaluation Limits

```simple
# src/app/heavy_compute/__init__.spl
__init__:
    # Increase limits for heavy compile-time computation
    comptime_max_iterations = 10_000_000
    comptime_max_memory = "256M"
    comptime_timeout = "60s"

    # Enable parallel comptime evaluation
    comptime_parallel = true
    comptime_threads = 4
```

### Module-Level Const Exports

```simple
# src/lib/constants/__init__.spl
__init__:
    # All const values in this module are public
    const_visibility_default = "public"

    # Generate documentation for const values
    const_doc_gen = true

# These are automatically public
const PI = 3.14159265358979
const E = 2.71828182845904
const GOLDEN_RATIO = 1.61803398874989
```

---

## Level 5: Project-Level Configuration (`simple.sdn`)

### Basic Comptime Settings

```sdn
[comptime]
# Enable const fn feature
enabled = true

# Default const evaluation limits
max_recursion = 500
max_iterations = 50000
max_memory = "64M"
timeout = "30s"

# Features
float_enabled = true
panic_enabled = false        # Panic in const fn is compile error

# Parallel evaluation
parallel = true
threads = "auto"             # Use available cores
```

### Profile-Specific Settings

```sdn
[comptime.profiles]
debug:
    # Relaxed limits for debugging
    max_recursion = 1000
    max_iterations = 100000
    max_memory = "256M"
    timeout = "120s"

    # Better error messages
    trace_enabled = true
    step_limit = 1000000

release:
    # Strict limits for release
    max_recursion = 500
    max_iterations = 50000
    max_memory = "64M"
    timeout = "30s"

    # Optimize const evaluation
    optimize_const = true
    cache_const_results = true

embedded:
    # Minimal limits for embedded
    max_recursion = 100
    max_iterations = 10000
    max_memory = "4M"
    timeout = "10s"

    # No floating point by default
    float_enabled = false
```

### Const Caching

```sdn
[comptime.cache]
# Cache const evaluation results
enabled = true
directory = ".cache/comptime"

# Cache invalidation
invalidate_on_source_change = true
invalidate_on_config_change = true

# Cache size limit
max_size = "1G"
```

---

## Const Evaluation Modes

### Mode: `const` (Strict)

```simple
# Must be evaluated at compile time, error if can't
const fn strict_func() -> i32:
    42

const VALUE = strict_func()    # OK
val runtime_val = strict_func()  # Also OK (const fn can run at runtime)
```

### Mode: `comptime` (Forced)

```simple
# MUST be evaluated at compile time, never at runtime
comptime fn forced_func() -> i32:
    expensive_computation()

const VALUE = forced_func()    # OK: compile time
# val x = forced_func()        # ERROR: comptime fn cannot be called at runtime
```

### Mode: `prefer_const` (Best Effort)

```simple
# Evaluate at compile time if possible, otherwise runtime
prefer_const fn flexible_func(x: i32) -> i32:
    x * x

const A = flexible_func(5)     # Compile time (arg is const)
val b = flexible_func(input)   # Runtime (arg is runtime)
```

### Configuration

```simple
__init__:
    # Default mode for functions
    comptime_mode_default = "prefer_const"   # "const", "comptime", "prefer_const"
```

---

## Const Fn Capabilities

### Capability Levels

```sdn
[comptime.capabilities]
# Level 0: Basic (always allowed)
arithmetic = true
bitwise = true
comparison = true
local_variables = true
conditionals = true
bounded_loops = true

# Level 1: Extended (configurable)
float = true
recursion = true
generics = true
arrays = true
structs = true

# Level 2: Advanced (opt-in)
strings = false              # String operations
collections = false          # Vec, HashMap at comptime
panic = false               # Panic in const fn
unbounded_loops = false      # Loops without const bound
```

### Per-Module Capabilities

```simple
# src/lib/math/__init__.spl
__init__:
    comptime_float = true
    comptime_recursion = true

# src/lib/strings/__init__.spl
__init__:
    comptime_strings = true
    comptime_collections = true
```

---

## Error Handling in Const Fn

### Const Panic

```simple
__init__:
    comptime_panic = true    # Enable panic in const fn

const fn safe_divide(a: i32, b: i32) -> i32:
    if b == 0:
        panic("Division by zero")   # Becomes compile error
    a / b

const RESULT = safe_divide(10, 2)   # OK: 5
const BAD = safe_divide(10, 0)      # COMPILE ERROR: Division by zero
```

### Const Result Type

```simple
const fn try_parse(s: str) -> Result<i32, str>:
    # Parsing logic...
    if valid:
        Ok(value)
    else:
        Err("Invalid format")

const PARSED = try_parse("42").unwrap()      # OK: 42
const BAD = try_parse("abc").unwrap()        # COMPILE ERROR: unwrap on Err
```

### Const Option Type

```simple
const fn find_index(arr: [i32; 10], target: i32) -> Option<i32>:
    for i in 0..10:
        if arr[i] == target:
            return Some(i)
    None

const DATA = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
const IDX = find_index(DATA, 5).unwrap()     # OK: 4
const BAD = find_index(DATA, 99).unwrap()    # COMPILE ERROR: unwrap on None
```

---

## Compile-Time Reflection

### Type Information

```simple
const fn type_name<T>() -> str:
    # Built-in: returns type name
    __type_name::<T>()

const fn size_of<T>() -> i32:
    # Built-in: returns size in bytes
    __size_of::<T>()

const fn align_of<T>() -> i32:
    # Built-in: returns alignment
    __align_of::<T>()

# Usage
const NAME = type_name<MyStruct>()    # "MyStruct"
const SIZE = size_of<MyStruct>()      # e.g., 24
const ALIGN = align_of<MyStruct>()    # e.g., 8
```

### Field Reflection

```simple
struct Point:
    x: f64
    y: f64
    z: f64

const fn field_count<T>() -> i32:
    __field_count::<T>()

const fn field_name<T>(index: i32) -> str:
    __field_name::<T>(index)

const fn field_offset<T>(index: i32) -> i32:
    __field_offset::<T>(index)

# Usage
const POINT_FIELDS = field_count<Point>()     # 3
const FIELD_0 = field_name<Point>(0)          # "x"
const OFFSET_Y = field_offset<Point>(1)       # 8
```

### Comptime Code Generation

```simple
# Generate serialization at compile time
comptime fn generate_serializer<T>() -> fn(T) -> [u8]:
    var code = ""
    for i in 0..field_count<T>():
        val name = field_name<T>(i)
        val offset = field_offset<T>(i)
        code += "result[{offset}..] = serialize(value.{name});\n"
    # Parse and return generated function
    parse_fn(code)

const POINT_SERIALIZER = generate_serializer<Point>()
```

---

## Complete Example

### Project Configuration (`simple.sdn`)

```sdn
[package]
name = "embedded-tables"
target = "embedded"

[comptime]
enabled = true
max_recursion = 500
max_iterations = 100000
max_memory = "32M"
float_enabled = true
panic_enabled = true

[comptime.cache]
enabled = true
directory = ".cache/comptime"
```

### Math Tables Module (`src/lib/math/__init__.spl`)

```simple
__init__:
    comptime_default = true
    comptime_float = true
    comptime_max_iterations = 1000000

    # Export all consts
    const_visibility_default = "public"
```

### Sin/Cos Tables (`src/lib/math/trig.spl`)

```simple
# All functions here are const by default (from __init__)

const PI: f64 = 3.14159265358979323846

fn deg_to_rad(deg: f64) -> f64:
    deg * PI / 180.0

fn generate_sin_table() -> [f64; 360]:
    var table: [f64; 360]
    for i in 0..360:
        table[i] = sin(deg_to_rad(i as f64))
    table

fn generate_cos_table() -> [f64; 360]:
    var table: [f64; 360]
    for i in 0..360:
        table[i] = cos(deg_to_rad(i as f64))
    table

# Computed at compile time
const SIN_TABLE: [f64; 360] = generate_sin_table()
const COS_TABLE: [f64; 360] = generate_cos_table()

# Fast lookup functions
fn fast_sin(deg: i32) -> f64:
    SIN_TABLE[deg % 360]

fn fast_cos(deg: i32) -> f64:
    COS_TABLE[deg % 360]
```

### CRC Tables (`src/lib/hash/crc.spl`)

```simple
const fn generate_crc32_table() -> [u32; 256]:
    var table: [u32; 256]
    for i in 0..256:
        var crc = i as u32
        for _ in 0..8:
            if crc & 1 != 0:
                crc = (crc >> 1) xor 0xEDB88320
            else:
                crc = crc >> 1
        table[i] = crc
    table

const CRC32_TABLE: [u32; 256] = generate_crc32_table()

fn crc32(data: [u8]) -> u32:
    var crc: u32 = 0xFFFFFFFF
    for byte in data:
        val index = ((crc xor byte as u32) & 0xFF) as i32
        crc = (crc >> 8) xor CRC32_TABLE[index]
    crc xor 0xFFFFFFFF
```

### Configuration Tables (`src/app/config.spl`)

```simple
__init__:
    comptime_default = true
    comptime_panic = true

# Computed at compile time with validation
const fn validate_config(config: Config) -> Config:
    if config.buffer_size < 64:
        panic("Buffer size must be >= 64")
    if config.buffer_size > 65536:
        panic("Buffer size must be <= 65536")
    if config.timeout_ms == 0:
        panic("Timeout must be > 0")
    config

const DEFAULT_CONFIG = validate_config(Config(
    buffer_size: 1024,
    timeout_ms: 5000,
    retries: 3
))

# Static assertions
static assert DEFAULT_CONFIG.buffer_size >= 64
static assert DEFAULT_CONFIG.buffer_size <= 65536
```

### Embedded Application (`src/main.spl`)

```simple
import lib.math.trig.{fast_sin, fast_cos}
import lib.hash.crc.crc32
import app.config.DEFAULT_CONFIG

fn main():
    # Use precomputed tables (zero runtime cost)
    val angle = 45
    val sin_val = fast_sin(angle)    # Table lookup
    val cos_val = fast_cos(angle)    # Table lookup

    # Use precomputed CRC table
    val data = [0x01, 0x02, 0x03]
    val checksum = crc32(data)

    # Use validated config
    init_with_config(DEFAULT_CONFIG)
```

---

## Summary

### Configuration Hierarchy

```
simple.sdn [comptime] (project defaults)
    └── __init__ comptime_* (module settings)
            └── const fn / comptime fn (function level)
                    └── comptime { } (block level)
                            └── const x = (expression level)
```

### Quick Reference

| Scope | Syntax | Meaning |
|-------|--------|---------|
| **Value** | `const X = expr` | Compile-time constant |
| **Function** | `const fn f()` | Can run at compile time |
| **Function** | `comptime fn f()` | Must run at compile time only |
| **Function** | `prefer_const fn f()` | Compile time if possible |
| **Function** | `runtime fn f()` | Never at compile time |
| **Block** | `comptime { }` | Force compile-time evaluation |
| **Module** | `__init__: comptime_default = true` | All fn const by default |
| **Project** | `[comptime] enabled = true` | Enable const evaluation |

### Const Fn Capabilities

| Capability | Default | `__init__` Setting |
|------------|---------|-------------------|
| Arithmetic | Yes | Always |
| Loops (bounded) | Yes | Always |
| Conditionals | Yes | Always |
| Recursion | Yes | `comptime_recursion` |
| Floating point | No | `comptime_float` |
| Panic | No | `comptime_panic` |
| Strings | No | `comptime_strings` |
| Collections | No | `comptime_collections` |

### Evaluation Limits

| Limit | Default | Setting |
|-------|---------|---------|
| Max recursion | 500 | `comptime_max_recursion` |
| Max iterations | 50000 | `comptime_max_iterations` |
| Max memory | 64M | `comptime_max_memory` |
| Timeout | 30s | `comptime_timeout` |
