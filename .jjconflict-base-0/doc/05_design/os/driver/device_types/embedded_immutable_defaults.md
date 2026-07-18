# Configurable Mutability Defaults for Embedded Systems

**Date**: 2026-01-31
**Question**: "for embedded freeze must default, can set on __init__?"

---

## The Problem

**Different platforms have different needs**:

| Platform | Default | Reason |
|----------|---------|--------|
| **General** | Mutable | User expectation, convenience |
| **Embedded** | Immutable | Memory constrained, no RefCell overhead |
| **WebAssembly** | Immutable | Smaller binary, faster startup |
| **High-performance** | Mutable | In-place updates faster |

**We need configurable defaults** based on target platform.

---

## Solution: Three-Level Configuration

### Level 1: Compiler Target (Global Default)

**Set default via compiler flag**:

```bash
# General mode (default): mutable collections
simple build

# Embedded mode: immutable collections by default
simple build --target=embedded

# WebAssembly mode: immutable collections
simple build --target=wasm
```

**Effect**:
```simple
// General mode:
val arr = [1, 2, 3]  # Type: Array (mutable, Rc<RefCell<Vec>>)

// Embedded mode:
val arr = [1, 2, 3]  # Type: FrozenArray (immutable, Rc<Vec>)
```

### Level 2: Module Attribute (Per-File Override)

**Set default for a specific file**:

```simple
# At top of file:
@target(embedded)  # This file uses embedded defaults

# Now arrays are immutable by default:
val arr = [1, 2, 3]  # FrozenArray (immutable)

# Explicitly mutable when needed:
var arr2 = mut [1, 2, 3]  # Array (mutable)
```

### Level 3: Type Annotation (Per-Variable Override)

**Override default for specific variable**:

```simple
# In embedded mode (immutable default):
val arr = [1, 2, 3]           # FrozenArray (immutable, default)
var arr2 = mut [1, 2, 3]      # Array (mutable, explicit)
val arr3: mut [i64] = [1, 2, 3]  # Array (mutable, type annotation)

# In general mode (mutable default):
var arr = [1, 2, 3]           # Array (mutable, default)
val arr2 = freeze([1, 2, 3])  # FrozenArray (immutable, explicit)
val arr3: const [i64] = [1, 2, 3]  # FrozenArray (immutable, type annotation)
```

---

## Compiler Targets

### Target: `general` (Default)

**Optimized for developer productivity**:

```bash
simple build  # Or: simple build --target=general
```

**Defaults**:
- Arrays: **Mutable** (`Rc<RefCell<Vec>>`)
- Dicts: **Mutable** (`Rc<RefCell<HashMap>>`)
- Performance: O(1) mutations, RefCell overhead
- Binary size: Larger (includes RefCell machinery)

**Code example**:
```simple
val arr = [1, 2, 3]  # Mutable by default
arr.push(4)  # OK
```

### Target: `embedded`

**Optimized for memory-constrained devices**:

```bash
simple build --target=embedded
```

**Defaults**:
- Arrays: **Immutable** (`Rc<Vec>`)
- Dicts: **Immutable** (`Rc<HashMap>`)
- Performance: No RefCell overhead
- Binary size: Smaller (no RefCell, no borrow checking)
- Memory: Less overhead (no borrow state)

**Code example**:
```simple
val arr = [1, 2, 3]  # Immutable by default
arr.push(4)  # ERROR: use mut [1, 2, 3] for mutable

var arr2 = mut [1, 2, 3]  # Explicitly mutable
arr2.push(4)  # OK
```

**Memory savings**:
```
General mode:
  Rc<RefCell<Vec<Value>>> = 8 (Rc) + 16 (RefCell) + 24 (Vec) = 48 bytes

Embedded mode:
  Rc<Vec<Value>> = 8 (Rc) + 24 (Vec) = 32 bytes

Savings: 16 bytes per array (33% reduction)
```

### Target: `wasm`

**Optimized for WebAssembly**:

```bash
simple build --target=wasm
```

**Defaults**:
- Arrays: **Immutable** (smaller WASM binary)
- Dicts: **Immutable**
- Performance: Fast startup, no RefCell
- Binary size: Minimal (dead code elimination)

### Target: `performance`

**Optimized for raw speed**:

```bash
simple build --target=performance
```

**Defaults**:
- Arrays: **Mutable** (in-place updates)
- Dicts: **Mutable**
- Performance: Aggressive optimizations
- Binary size: Larger (includes all optimization code)

---

## Runtime Configuration (Advanced)

### Option A: Compile-Time Configuration File

**File**: `simple.config.toml`

```toml
[build]
target = "embedded"

[embedded]
default_array_mutability = "immutable"
default_dict_mutability = "immutable"
enable_refcell = false  # Disable RefCell entirely

[embedded.memory]
stack_size = 4096       # 4KB stack
heap_size = 65536       # 64KB heap
```

**Usage**:
```bash
simple build --config=simple.config.toml
```

### Option B: Module-Level Pragma

**Syntax**:
```simple
# At top of file:
#[target = "embedded"]
#[default_mutability = "immutable"]

val arr = [1, 2, 3]  # Immutable (follows pragma)
```

### Option C: Conditional Compilation

**Syntax**:
```simple
# Use different defaults based on target:
#[cfg(target = "embedded")]
const DEFAULT_MUTABILITY = "immutable"

#[cfg(target = "general")]
const DEFAULT_MUTABILITY = "mutable"

# Use in code:
val arr = [1, 2, 3]  # Mutability depends on target
```

---

## Implementation

### Step 1: Add Target to Compiler Options (1-2h)

**File**: `rust/compiler/src/config.rs`

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum CompilationTarget {
    General,     // Default: mutable collections
    Embedded,    // Default: immutable collections
    Wasm,        // Default: immutable collections
    Performance, // Default: mutable collections
}

pub struct CompilerConfig {
    pub target: CompilationTarget,
    pub default_array_mutability: Mutability,
    pub default_dict_mutability: Mutability,
}

impl CompilerConfig {
    pub fn for_target(target: CompilationTarget) -> Self {
        match target {
            CompilationTarget::General => Self {
                target,
                default_array_mutability: Mutability::Mutable,
                default_dict_mutability: Mutability::Mutable,
            },
            CompilationTarget::Embedded => Self {
                target,
                default_array_mutability: Mutability::Immutable,
                default_dict_mutability: Mutability::Immutable,
            },
            CompilationTarget::Wasm => Self {
                target,
                default_array_mutability: Mutability::Immutable,
                default_dict_mutability: Mutability::Immutable,
            },
            CompilationTarget::Performance => Self {
                target,
                default_array_mutability: Mutability::Mutable,
                default_dict_mutability: Mutability::Mutable,
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mutability {
    Mutable,
    Immutable,
}
```

### Step 2: Parse Module Attributes (2-3h)

**File**: `rust/parser/src/attributes.rs`

```rust
// Parse: @target(embedded)
pub fn parse_module_attribute() -> Result<ModuleAttribute, ParseError> {
    expect_token(Token::At)?;
    let attr_name = parse_identifier()?;

    match attr_name.as_str() {
        "target" => {
            expect_token(Token::LeftParen)?;
            let target = parse_identifier()?;
            expect_token(Token::RightParen)?;

            let target_enum = match target.as_str() {
                "embedded" => CompilationTarget::Embedded,
                "general" => CompilationTarget::General,
                "wasm" => CompilationTarget::Wasm,
                "performance" => CompilationTarget::Performance,
                _ => return Err(ParseError::semantic("unknown target"))
            };

            Ok(ModuleAttribute::Target(target_enum))
        }
        _ => Err(ParseError::semantic("unknown attribute"))
    }
}
```

### Step 3: Apply Default Mutability in Type Inference (3-4h)

**File**: `rust/compiler/src/interpreter_call/mod.rs`

```rust
Expr::ArrayLiteral { elements } => {
    let values = evaluate_elements(elements)?;

    // Determine mutability based on:
    // 1. Explicit type annotation (overrides default)
    // 2. Module attribute (overrides target)
    // 3. Compilation target (global default)

    let mutability = if let Some(type_ann) = expected_type {
        type_ann.mutability()  // Explicit type annotation wins
    } else if let Some(module_attr) = current_module.attribute {
        module_attr.default_mutability()  // Module attribute
    } else {
        config.default_array_mutability  // Global default from target
    };

    match mutability {
        Mutability::Mutable => {
            Ok(Value::Array(Rc::new(RefCell::new(values))))
        }
        Mutability::Immutable => {
            Ok(Value::FrozenArray(Rc::new(values)))
        }
    }
}
```

### Step 4: CLI Flag Support (1-2h)

**File**: `rust/driver/src/main.rs`

```rust
#[derive(Parser)]
struct Cli {
    #[arg(long, default_value = "general")]
    target: String,

    // ... other args
}

fn main() {
    let cli = Cli::parse();

    let target = match cli.target.as_str() {
        "embedded" => CompilationTarget::Embedded,
        "general" => CompilationTarget::General,
        "wasm" => CompilationTarget::Wasm,
        "performance" => CompilationTarget::Performance,
        _ => {
            eprintln!("Unknown target: {}", cli.target);
            std::process::exit(1);
        }
    };

    let config = CompilerConfig::for_target(target);

    // Pass config to compiler...
}
```

---

## Examples

### Example 1: Embedded Sensor Code

```simple
# sensor_read.spl
@target(embedded)  # Use embedded defaults

# Immutable by default (no RefCell overhead):
val readings = [0.0, 0.0, 0.0, 0.0]  # FrozenArray
val calibration = {"offset": 1.5, "scale": 2.0}  # FrozenDict

fn read_sensors() -> [f64]:
    # Return new array (functional style)
    [
        read_sensor(0) + calibration["offset"],
        read_sensor(1) + calibration["offset"],
        read_sensor(2) + calibration["offset"],
        read_sensor(3) + calibration["offset"],
    ]

# Mutable only when needed:
var buffer = mut [0u8; 1024]  # Explicit mutable buffer
fn fill_buffer():
    for i in 0..1024:
        buffer[i] = read_byte()
```

### Example 2: WebAssembly Application

```simple
# app.spl
@target(wasm)  # Use wasm defaults

# Immutable by default (smaller binary):
val APP_CONFIG = {
    "title": "My App",
    "version": "1.0.0",
}

val ROUTES = [
    "/home",
    "/about",
    "/contact",
]

# Mutable state when needed:
var user_state = mut {
    "logged_in": false,
    "username": "",
}

fn login(username: text):
    user_state["logged_in"] = true
    user_state["username"] = username
```

### Example 3: High-Performance Server

```simple
# server.spl
@target(performance)  # Use performance defaults

# Mutable by default (in-place updates):
var connection_pool = []
var request_queue = []

fn handle_request(req: Request):
    request_queue.push(req)  # O(1) in-place mutation

fn process_requests():
    while request_queue.len() > 0:
        val req = request_queue.pop()  # O(1) mutation
        handle(req)
```

### Example 4: Mixed Mode (Explicit Overrides)

```simple
# data_processing.spl
@target(embedded)  # Default: immutable

# Immutable (default):
val constants = [PI, E, GOLDEN_RATIO]

# Explicitly mutable (override default):
var cache = mut {}
fn get_cached(key: text) -> Option<Value>:
    cache.get(key).or_else(|| {
        val value = expensive_computation(key)
        cache[key] = value
        Some(value)
    })

# Explicitly immutable (redundant but clear):
val lookup_table: const {text: i64} = {
    "one": 1,
    "two": 2,
    "three": 3,
}
```

---

## Build Profiles

### Profile: Development (Default)

```bash
simple build
# Or: simple build --profile=dev
```

**Settings**:
- Target: `general`
- Default: Mutable collections
- Optimizations: None
- Debug info: Full
- Checks: All enabled (bounds, borrow, overflow)

### Profile: Embedded Release

```bash
simple build --profile=embedded-release
```

**Settings**:
- Target: `embedded`
- Default: Immutable collections
- Optimizations: Size (`-Os`)
- Debug info: None
- Checks: Minimal (remove bounds checks)
- No std library (optional)
- LTO: Full

### Profile: WebAssembly

```bash
simple build --profile=wasm
```

**Settings**:
- Target: `wasm`
- Default: Immutable collections
- Optimizations: Size + speed (`-Os -O2`)
- WASM features: SIMD, threads (optional)
- Binary format: `.wasm`

### Profile: Performance

```bash
simple build --profile=performance
```

**Settings**:
- Target: `performance`
- Default: Mutable collections
- Optimizations: Maximum (`-O3`)
- Inlining: Aggressive
- SIMD: Enabled
- PGO: Enabled (optional)

---

## Configuration File Format

**File**: `simple.toml` (project root)

```toml
[package]
name = "my-embedded-app"
version = "1.0.0"

[build]
default-target = "embedded"

[target.embedded]
default-mutability = "immutable"
stack-size = 4096
heap-size = 65536
panic = "abort"  # Don't unwind on panic (smaller binary)

[target.embedded.features]
refcell = false  # Disable RefCell entirely
fmt = false      # No string formatting (save space)
std = false      # No standard library

[target.general]
default-mutability = "mutable"
features = ["std", "refcell", "fmt"]

[profile.dev]
opt-level = 0
debug = true

[profile.release]
opt-level = 3
lto = true
strip = true
```

**Usage**:
```bash
# Use embedded target from config:
simple build

# Override target:
simple build --target=general

# Use specific profile:
simple build --profile=release
```

---

## Memory Comparison

### General Mode (Mutable Default)

```rust
// Array storage:
Rc<RefCell<Vec<Value>>> = {
    Rc: 8 bytes (pointer + ref count)
    RefCell: 16 bytes (borrow state + pointer)
    Vec: 24 bytes (ptr + len + capacity)
} = 48 bytes per array

// Dict storage:
Rc<RefCell<HashMap<String, Value>>> = {
    Rc: 8 bytes
    RefCell: 16 bytes
    HashMap: 48 bytes (capacity-dependent)
} = 72 bytes per dict
```

### Embedded Mode (Immutable Default)

```rust
// Array storage:
Rc<Vec<Value>> = {
    Rc: 8 bytes (pointer + ref count)
    Vec: 24 bytes (ptr + len + capacity)
} = 32 bytes per array (33% reduction)

// Dict storage:
Rc<HashMap<String, Value>> = {
    Rc: 8 bytes
    HashMap: 48 bytes
} = 56 bytes per dict (22% reduction)
```

**Savings for 100 arrays + 50 dicts**:
- General: 100×48 + 50×72 = 8400 bytes
- Embedded: 100×32 + 50×56 = 6000 bytes
- **Saved: 2400 bytes (29% reduction)**

---

## Implementation Effort

| Step | Description | Effort |
|------|-------------|--------|
| 1 | Add CompilationTarget enum and config | 1-2h |
| 2 | Parse module attributes (`@target`) | 2-3h |
| 3 | Apply default mutability in type inference | 3-4h |
| 4 | CLI flag support (`--target`) | 1-2h |
| 5 | Configuration file parsing | 2-3h |
| 6 | Build profiles (dev, release, embedded) | 2-3h |
| 7 | Documentation and testing | 2-3h |

**Total**: 13-20 hours

---

## Answer to Your Question

### Q: "for embedded freeze must default"
**A**: YES! Use `--target=embedded` or `@target(embedded)` to make immutable the default.

### Q: "can set on __init__?"
**A**: Not exactly `__init__`, but you can set it via:
1. **Compiler flag**: `simple build --target=embedded`
2. **Module attribute**: `@target(embedded)` at top of file
3. **Config file**: `simple.toml` with `default-target = "embedded"`

**Example**:
```simple
@target(embedded)  # Set at module level

val arr = [1, 2, 3]  # Immutable by default (no RefCell)
var buf = mut [0; 1024]  # Explicit mutable when needed
```

**Benefits for embedded**:
- 33% less memory per collection
- No RefCell borrow checking overhead
- Smaller binary size
- Functional style (better for safety-critical code)

---

## Integration with Previous Designs

**Combined system**:

```simple
# General mode (default):
val arr = [1, 2, 3]          # Mutable
val arr2 = freeze([1, 2, 3]) # Immutable (explicit)

# Embedded mode:
@target(embedded)
val arr = [1, 2, 3]          # Immutable (default)
var arr2 = mut [1, 2, 3]     # Mutable (explicit)
```

**Best of both worlds**!
