# SFFI External Library Pattern Design

**Status**: Implemented
**Created**: 2026-02-08
**Updated**: 2026-02-08

## Overview

This document describes the **three-tier pattern** for wrapping external libraries with Simple FFI (SFFI). The pattern supports **two Tier 1 backends** selected via the `lang` field in `.wrapper_spec` files:

| Backend | `lang` field | Use case | Tier 1 output |
|---------|-------------|----------|---------------|
| **C++** | `lang: cpp` (default) | C/C++ libraries (PyTorch, OpenCV, SQLite) | cxx bridge + C++ wrapper (`bridge.h`, `bridge.cpp`, `lib.rs`) |
| **Rust** | `lang: rust` | Rust crates (regex, reqwest, gilrs) | Handle table + direct Rust FFI (`lib.rs` only) |

## Problem Statement

The existing two-tier SFFI pattern works for functionality built into the Simple runtime:
- **Tier 1**: `extern fn rt_*` declarations
- **Tier 2**: Simple wrapper functions

But what about external libraries? These come in two flavors:
- **C/C++ libraries** (PyTorch, OpenCV, SQLite) - need a cxx bridge
- **Rust crates** (regex, reqwest, gilrs) - can use direct Rust FFI with handle tables

We need a **three-tier pattern** with backend selection to bridge both kinds of external libraries to Simple.

## Three-Tier SFFI Pattern

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ Tier 3: Simple API Layer (src/lib/*/mod.spl)              │
│   - User-facing API                                         │
│   - Type safety, error handling                            │
│   - Idiomatic Simple patterns                              │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼ calls
┌─────────────────────────────────────────────────────────────┐
│ Tier 2: SFFI Bindings (src/lib/*/ffi.spl)                 │
│   - extern fn declarations                                  │
│   - Raw FFI bindings (rt_* prefix)                         │
│   - Minimal type conversions                               │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼ links to
┌─────────────────────────────────────────────────────────────┐
│ Tier 1: Native Wrapper (.build/rust/ffi_*/src/lib.rs)     │
│   lang: cpp  -> cxx bridge + C++ wrapper                   │
│   lang: rust -> Handle table + direct Rust FFI             │
│   #[no_mangle] pub extern "C" exports                      │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼ links to
┌─────────────────────────────────────────────────────────────┐
│ Tier 0: External Library                                   │
│   C++:  libtorch.so, libopencv_core.so, libsqlite3.so     │
│   Rust: regex crate, reqwest crate, gilrs crate           │
└─────────────────────────────────────────────────────────────┘
```

**Key design decision**: Tiers 2 and 3 are **identical** regardless of the Tier 1 backend. The `lang` field only affects Tier 1 code generation. This means Simple-side code is backend-agnostic.

### Tier 0: External C/C++ Library

The original library (e.g., libtorch.so, libopencv.so). This is a system dependency.

**Characteristics:**
- Pre-installed on the system or downloaded separately
- C/C++ ABI
- May have complex C++ APIs
- Requires linking

**Example**: PyTorch's libtorch
- Location: `/usr/local/lib/libtorch.so` or conda env
- C++ API: `torch::Tensor`, `torch::nn::Module`, etc.
- C API: Limited, mostly for Python bindings

### Tier 1: Native Wrapper (Two Backends)

**Location**: `.build/rust/ffi_<library>/`

**Purpose**: Minimal native code that:
1. Provides C FFI bindings (`#[no_mangle] pub extern "C"`)
2. Converts between Rust/C types and Simple types
3. Handles memory safety
4. Links to the external library

**Backend selection**: Controlled by the `lang` field in `.wrapper_spec` files.

#### Backend A: C++ Libraries (`lang: cpp`)

Uses the **cxx bridge** pattern for C++ interop. Generates:
- `lib.rs` - Rust side with `#[cxx::bridge]`
- `bridge.h` - C++ bridge header
- `bridge.cpp` - C++ bridge implementation
- `build.rs` - Find system library

**Example**: PyTorch wrapper (`lang: cpp`)

```rust
// .build/rust/ffi_torch/src/lib.rs
// cxx bridge pattern for C++ interop

#[link(name = "torch")]
extern "C" {
    fn at_zeros(dims: *const i64, ndim: usize) -> *mut c_void;
    fn at_free(tensor: *mut c_void);
}

pub struct SimpleTorchTensor {
    ptr: *mut c_void,
}

#[no_mangle]
pub extern "C" fn simple_torch_tensor_zeros(
    dims: *const i64,
    ndim: usize
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_zeros(dims, ndim);
        Box::into_raw(Box::new(SimpleTorchTensor { ptr }))
    }
}
```

#### Backend B: Rust Crates (`lang: rust`)

Uses the **handle table** pattern for direct Rust crate wrapping. Generates:
- `Cargo.toml` - Dependencies on the Rust crate
- `src/lib.rs` - Handle table + `#[no_mangle]` exports

No `bridge.h`, `bridge.cpp`, `build.rs`, or cxx dependency needed.

**Handle table pattern**:
- `HashMap<i64, RustObject>` stores live objects
- `AtomicI64` counter for unique handle IDs
- All functions take/return `i64` handles (0 = invalid)
- Thread-safe via `Mutex`

**Example**: Regex wrapper (`lang: rust`)

```rust
// .build/rust/ffi_regex/src/lib.rs
// Handle table pattern for Rust crates

use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicI64, Ordering};

static REGEXHANDLE_NEXT_ID: AtomicI64 = AtomicI64::new(1);
static REGEXHANDLE_HANDLES: Mutex<Option<HashMap<i64, regex::Regex>>> =
    Mutex::new(None);

fn regexhandle_alloc(obj: regex::Regex) -> i64 {
    let id = REGEXHANDLE_NEXT_ID.fetch_add(1, Ordering::SeqCst);
    let mut guard = REGEXHANDLE_HANDLES.lock().unwrap();
    let map = guard.get_or_insert_with(HashMap::new);
    map.insert(id, obj);
    id
}

#[no_mangle]
pub extern "C" fn rt_regex_new(pattern: *const c_char) -> i64 {
    unsafe {
        let pattern_s = cstr_to_str(pattern);
        match regex::Regex::new(pattern_s) {
            Ok(result) => regexhandle_alloc(result),
            Err(_) => 0,  // 0 = invalid handle
        }
    }
}
```

**Build Configuration** (Rust backend): `Cargo.toml`

```toml
[package]
name = "simple-regex-ffi"
version = "0.1.0"
edition = "2021"

[lib]
name = "simple_regex_ffi"
crate-type = ["cdylib"]

[dependencies]
regex = "1"
```

**Build Configuration** (C++ backend): `Cargo.toml`

```toml
[package]
name = "simple-torch-ffi"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib"]

[build-dependencies]
pkg-config = "0.3"

[package.metadata.simple]
library = "torch"
system-deps = ["libtorch >= 2.0"]
```

### Tier 2: SFFI Bindings (Simple)

**Location**: `src/lib/<library>/ffi.spl`

**Purpose**: Simple-side FFI declarations that match Tier 1's C exports

**Characteristics:**
- `extern fn` declarations
- Prefix: `rt_torch_*` (follows Simple FFI convention)
- Opaque handle types
- No implementation (runtime links to Rust dylib)

**Example**: PyTorch SFFI bindings

```simple
# src/lib/torch/ffi.spl
# SFFI bindings to Tier 1 Rust wrapper

# --- Opaque Handle Types ---
# TorchTensor is an opaque reference to C++ torch::Tensor
extern type TorchTensorHandle

# --- Tensor Creation ---
extern fn rt_torch_tensor_zeros(dims: [i64]) -> TorchTensorHandle
extern fn rt_torch_tensor_ones(dims: [i64]) -> TorchTensorHandle
extern fn rt_torch_tensor_from_array(data: [f64], dims: [i64]) -> TorchTensorHandle
extern fn rt_torch_tensor_free(handle: TorchTensorHandle)

# --- Tensor Operations ---
extern fn rt_torch_tensor_add(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tensor_mul(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tensor_matmul(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle

# --- Tensor Properties ---
extern fn rt_torch_tensor_shape(handle: TorchTensorHandle) -> [i64]
extern fn rt_torch_tensor_ndim(handle: TorchTensorHandle) -> i64
extern fn rt_torch_tensor_numel(handle: TorchTensorHandle) -> i64
extern fn rt_torch_tensor_to_array(handle: TorchTensorHandle) -> [f64]

# --- Activations ---
extern fn rt_torch_relu(x: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_sigmoid(x: TorchTensorHandle) -> TorchTensorHandle
extern fn rt_torch_tanh(x: TorchTensorHandle) -> TorchTensorHandle

# --- Device Management ---
extern fn rt_torch_cuda_available() -> bool
extern fn rt_torch_tensor_to_device(handle: TorchTensorHandle, device: text) -> TorchTensorHandle

# --- Availability Check ---
extern fn rt_torch_available() -> bool
extern fn rt_torch_version() -> text
```

### Tier 3: Simple API Layer

**Location**: `src/lib/<library>/mod.spl`

**Purpose**: User-facing idiomatic Simple API

**Characteristics:**
- **Type safety**: Wraps opaque handles in Simple classes
- **Resource management**: RAII pattern (constructor/destructor)
- **Error handling**: Simple error types, not raw C errors
- **Convenience**: High-level operations, method chaining

**Example**: PyTorch Simple API

```simple
# src/lib/torch/mod.spl
# User-facing PyTorch API for Simple

use lib.torch.ffi.*

# --- High-Level Tensor Type ---
class Tensor:
    handle: TorchTensorHandle
    owns_handle: bool

    # Constructor (private - use static factories)
    fn init(handle: TorchTensorHandle):
        self.handle = handle
        self.owns_handle = true

    # Destructor (called when tensor goes out of scope)
    fn drop():
        if self.owns_handle:
            rt_torch_tensor_free(self.handle)

    # --- Static Factory Methods ---
    static fn zeros(shape: [i64]) -> Tensor:
        val handle = rt_torch_tensor_zeros(shape)
        Tensor(handle: handle, owns_handle: true)

    static fn ones(shape: [i64]) -> Tensor:
        val handle = rt_torch_tensor_ones(shape)
        Tensor(handle: handle, owns_handle: true)

    static fn from_array(data: [f64], shape: [i64]) -> Tensor:
        val handle = rt_torch_tensor_from_array(data, shape)
        Tensor(handle: handle, owns_handle: true)

    # --- Properties ---
    fn shape() -> [i64]:
        rt_torch_tensor_shape(self.handle)

    fn ndim() -> i64:
        rt_torch_tensor_ndim(self.handle)

    fn numel() -> i64:
        rt_torch_tensor_numel(self.handle)

    fn to_array() -> [f64]:
        rt_torch_tensor_to_array(self.handle)

    # --- Operations (return new tensors) ---
    fn add(other: Tensor) -> Tensor:
        val result_handle = rt_torch_tensor_add(self.handle, other.handle)
        Tensor(handle: result_handle, owns_handle: true)

    fn mul(other: Tensor) -> Tensor:
        val result_handle = rt_torch_tensor_mul(self.handle, other.handle)
        Tensor(handle: result_handle, owns_handle: true)

    fn matmul(other: Tensor) -> Tensor:
        val result_handle = rt_torch_tensor_matmul(self.handle, other.handle)
        Tensor(handle: result_handle, owns_handle: true)

    # --- Activations ---
    fn relu() -> Tensor:
        val result_handle = rt_torch_relu(self.handle)
        Tensor(handle: result_handle, owns_handle: true)

    fn sigmoid() -> Tensor:
        val result_handle = rt_torch_sigmoid(self.handle)
        Tensor(handle: result_handle, owns_handle: true)

    fn tanh() -> Tensor:
        val result_handle = rt_torch_tanh(self.handle)
        Tensor(handle: result_handle, owns_handle: true)

    # --- Device Management ---
    fn to_device(device: text) -> Tensor:
        val result_handle = rt_torch_tensor_to_device(self.handle, device)
        Tensor(handle: result_handle, owns_handle: true)

    fn cuda() -> Tensor:
        self.to_device("cuda")

    fn cpu() -> Tensor:
        self.to_device("cpu")

# --- Operator Overloading ---
fn +(a: Tensor, b: Tensor) -> Tensor:
    a.add(b)

fn *(a: Tensor, b: Tensor) -> Tensor:
    a.mul(b)

fn @(a: Tensor, b: Tensor) -> Tensor:
    a.matmul(b)

# --- Module-Level Functions ---
fn torch_available() -> bool:
    rt_torch_available()

fn torch_version() -> text:
    rt_torch_version()

fn cuda_available() -> bool:
    rt_torch_cuda_available()
```

## Directory Structure

```
simple/
├── .build/rust/              # Tier 1: Native wrappers (auto-generated)
│   ├── ffi_torch/           # C++ backend (lang: cpp)
│   │   ├── Cargo.toml
│   │   ├── build.rs
│   │   ├── src/lib.rs       # cxx bridge + C FFI exports
│   │   ├── bridge.h         # C++ bridge header
│   │   └── bridge.cpp       # C++ bridge impl
│   ├── ffi_regex/           # Rust backend (lang: rust)
│   │   ├── Cargo.toml       # Depends on regex crate
│   │   └── src/lib.rs       # Handle table + C FFI exports
│   └── ffi_opencv/
│       └── ...
│
├── examples/                 # Wrapper spec files
│   ├── torch.wrapper_spec   # C++ backend example
│   └── regex.wrapper_spec   # Rust backend example
│
├── src/app/wrapper_gen/     # Wrapper generator
│   ├── mod.spl              # Main entry + CLI
│   ├── spec_parser.spl      # .wrapper_spec parser
│   ├── tier1_gen.spl        # Tier 1: C++ backend (cxx bridge)
│   ├── tier1_rust_gen.spl   # Tier 1: Rust backend (handle tables)
│   ├── tier2_gen.spl        # Tier 2: Simple extern fn declarations
│   └── tier3_gen.spl        # Tier 3: Simple API scaffold
│
├── src/lib/                  # Simple libraries
│   ├── torch/               # Tier 2 + 3 (same for both backends)
│   │   ├── mod.spl          # Tier 3: User-facing API
│   │   ├── ffi.spl          # Tier 2: SFFI bindings
│   │   └── nn.spl           # Neural network layers
│   └── ...
│
└── src/lib/pure/            # Pure Simple fallbacks
    ├── torch_ffi.spl        # Pure Simple tensor ops
    └── ...
```

## Build Integration

### Build System Changes

The Simple build system needs to:
1. **Detect external dependencies** (via `simple.sdn` manifest)
2. **Build Rust wrappers** (Tier 1) as needed
3. **Link dylibs** into the runtime
4. **Validate SFFI declarations** match Rust exports

### Package Manifest

```sdn
# simple.sdn
package:
  name: my-ml-app
  version: 0.1.0

dependencies:
  torch:
    version: 2.0
    backend: ffi  # Use FFI bindings (vs pure)

system-deps:
  # System libraries that must be present
  libtorch: ">= 2.0.0"
  cuda: ">= 11.8"  # Optional
```

### Build Commands

```bash
# Check system dependencies
bin/simple build check-deps

# Build Rust FFI wrappers
bin/simple build ffi --all

# Build specific FFI wrapper
bin/simple build ffi torch

# Clean FFI artifacts
bin/simple build clean-ffi
```

## Feature Detection

The Simple code should gracefully handle missing libraries:

```simple
# src/lib/torch/mod.spl

fn get_backend() -> text:
    if rt_torch_available():
        "ffi"      # FFI backend available
    else:
        "pure"     # Fall back to pure Simple

fn zeros(shape: [i64]) -> Tensor:
    if get_backend() == "ffi":
        Tensor.zeros_ffi(shape)    # Use PyTorch FFI
    else:
        Tensor.zeros_pure(shape)   # Use pure Simple impl
```

## Testing Strategy

### Unit Tests

```simple
# test/lib/torch_spec.spl
use lib.torch.*

describe "Torch FFI":
    it "creates zero tensors":
        val t = Tensor.zeros([2, 3])
        expect(t.shape()).to_equal([2, 3])
        expect(t.numel()).to_equal(6)

    it "performs addition":
        val a = Tensor.ones([2, 2])
        val b = Tensor.ones([2, 2])
        val c = a + b
        expect(c.to_array()).to_equal([2.0, 2.0, 2.0, 2.0])

    it "handles CUDA if available":
        if cuda_available():
            val t = Tensor.zeros([10, 10]).cuda()
            # GPU operations
```

### Integration Tests

```simple
# test/integration/ml_pipeline_spec.spl
use lib.torch.*

describe "ML Pipeline":
    it "runs forward pass":
        val input = Tensor.from_array([1.0, 2.0, 3.0], [1, 3])
        val weights = Tensor.zeros([3, 2])
        val output = input @ weights
        expect(output.shape()).to_equal([1, 2])
```

## Advantages

1. **Thin Rust layer**: Minimal Rust code (just FFI safety)
2. **All logic in Simple**: Business logic, error handling, API design in Simple
3. **Gradual migration**: Can mix FFI and pure Simple implementations
4. **Type safety**: Simple type system catches errors at compile time
5. **Resource safety**: RAII pattern prevents memory leaks

## Disadvantages

1. **Extra layer**: More indirection than direct C bindings
2. **Build complexity**: Requires Rust toolchain + external libraries
3. **ABI stability**: Changes in C library ABI require Rust wrapper updates
4. **Platform-specific**: Need to handle different library locations per OS

## Alternatives Considered

### Alternative 1: Direct C Bindings in Simple

Skip Tier 1 (Rust), call C functions directly from Simple:

```simple
# Direct C FFI (not recommended)
extern fn at_zeros(dims: *i64, ndim: i32) -> *void
```

**Rejected because**:
- Unsafe: No memory safety guarantees
- Complex: Manual pointer arithmetic in Simple
- Error-prone: Easy to introduce memory leaks

### Alternative 2: Rust-Only Implementation

Implement everything in Rust, expose minimal API to Simple:

**Rejected because**:
- Against "Simple-first" philosophy
- All logic would be in Rust, not Simple
- Harder for Simple developers to contribute

### Alternative 3: Pure Simple Only

No FFI, implement everything in pure Simple:

**Rejected because**:
- Performance: Can't match optimized C++ libraries
- Duplication: Re-implementing PyTorch/OpenCV is massive effort
- CUDA: Can't access GPU without FFI

### Alternative 4: Single Backend (C++ only)

Only support cxx bridge for all external libraries:

**Rejected because**:
- Unnecessary overhead for Rust crates (cxx bridge generates C++ for Rust-to-Rust)
- Handle table pattern is simpler and more direct for Rust crates
- Both backends use the same Tiers 2 and 3, so dual support is low cost

## Implementation Status

### Phase 1: Design and Infrastructure - COMPLETE
- [x] Design three-tier pattern with dual backend support
- [x] Implement `.wrapper_spec` parser with `lang` field
- [x] Implement Tier 1 C++ generator (cxx bridge: `tier1_gen.spl`)
- [x] Implement Tier 1 Rust generator (handle tables: `tier1_rust_gen.spl`)
- [x] Implement Tier 2 generator (`tier2_gen.spl`)
- [x] Implement Tier 3 generator (`tier3_gen.spl`)
- [x] Create wrapper generator CLI (`wrapper-gen`)
- [x] Document in CLAUDE.md and SFFI skill
- [x] Create example specs: `torch.wrapper_spec` (C++), `regex.wrapper_spec` (Rust)

### Phase 2: Library Wrappers - In Progress
- [ ] Build and test regex Tier 1 wrapper
- [ ] Build and test HTTP Tier 1 wrapper
- [ ] Build and test gamepad Tier 1 wrapper
- [ ] Build and test other library wrappers

### Phase 3: Runtime Integration
- [ ] Dynamic library loading for SFFI modules
- [ ] Test on Linux/macOS/Windows
- [ ] Package FFI wrappers with Simple runtime

## See Also

- **SFFI Skill**: `.claude/skills/sffi.md`
- **Wrapper Generator**: `src/app/wrapper_gen/`
- **Pure Simple Torch**: `src/lib/pure/torch_ffi.spl`
- **Build System**: `src/app/build/`
- **Package Manifest**: `simple.sdn`
