# SFFI External Libraries Quick Start Guide

**Last Updated**: 2026-02-08

## Overview

This guide shows you how to wrap external C/C++ libraries (PyTorch, OpenCV, SQLite, etc.) for use in Simple using the **three-tier SFFI pattern**.

## When to Use Each Pattern

### Two-Tier Pattern (Runtime Built-ins)

Use for functionality **built into** the Simple runtime:

```simple
# File I/O, process management, system calls
extern fn rt_file_read(path: text) -> text
fn file_read(path: text) -> text:
    rt_file_read(path)
```

**Location**: `src/app/io/mod.spl`

### Three-Tier Pattern (External Libraries)

Use for **external** C/C++ libraries not in the runtime:

- PyTorch (libtorch.so)
- OpenCV (libopencv.so)
- SQLite (libsqlite3.so)
- TensorFlow, etc.

## Three-Tier Architecture

```
┌─────────────────────────────────────┐
│ Tier 3: Simple API                  │  ← User code imports this
│   class Tensor:                     │
│     fn zeros(shape) -> Tensor       │
└──────────────┬──────────────────────┘
               │ calls
┌──────────────▼──────────────────────┐
│ Tier 2: SFFI Bindings               │  ← extern declarations
│   extern fn rt_torch_tensor_zeros() │
└──────────────┬──────────────────────┘
               │ links to
┌──────────────▼──────────────────────┐
│ Tier 1: Thin Rust Wrapper           │  ← Memory safety only
│   #[no_mangle] pub extern "C"       │
│   fn simple_torch_tensor_zeros()    │
└──────────────┬──────────────────────┘
               │ links to
┌──────────────▼──────────────────────┐
│ Tier 0: External Library            │  ← libtorch.so
│   torch::zeros(...)                 │
└─────────────────────────────────────┘
```

## Step-by-Step: Wrapping a New Library

### Step 1: Create Rust Wrapper (Tier 1)

**Location**: `.build/rust/ffi_<library>/`

**Files**:
- `Cargo.toml` - Package manifest
- `build.rs` - Find system library
- `src/lib.rs` - FFI exports

**Example**: `.build/rust/ffi_opencv/`

```rust
// .build/rust/ffi_opencv/src/lib.rs

#[no_mangle]
pub extern "C" fn simple_opencv_imread(
    path: *const c_char,
) -> *mut SimpleOpenCVMat {
    // Thin wrapper - just FFI safety
    unsafe {
        let c_str = CStr::from_ptr(path);
        let path_str = c_str.to_str().unwrap();
        let mat = cv_imread(path_str);  // Call C++ OpenCV
        Box::into_raw(Box::new(SimpleOpenCVMat::new(mat)))
    }
}
```

**Key Points**:
- Prefix: `simple_<library>_*`
- ABI: `#[no_mangle] pub extern "C"`
- Opaque handles (e.g., `SimpleOpenCVMat`)
- No business logic - just memory safety

### Step 2: Create SFFI Bindings (Tier 2)

**Location**: `src/lib/<library>/ffi.spl`

```simple
# src/lib/opencv/ffi.spl

# Opaque handle type
extern type OpenCVMatHandle

# FFI declarations
extern fn rt_opencv_imread(path: text) -> OpenCVMatHandle
extern fn rt_opencv_imwrite(path: text, mat: OpenCVMatHandle) -> bool
extern fn rt_opencv_mat_free(handle: OpenCVMatHandle)
```

**Key Points**:
- Prefix: `rt_<library>_*`
- Opaque types for C++ objects
- Minimal - just declarations

### Step 3: Create Simple API (Tier 3)

**Location**: `src/lib/<library>/mod.spl`

```simple
# src/lib/opencv/mod.spl

use lib.opencv.ffi.*

class Mat:
    handle: OpenCVMatHandle
    owns_handle: bool

    static fn imread(path: text) -> Mat:
        val handle = rt_opencv_imread(path)
        Mat(handle: handle, owns_handle: true)

    fn imwrite(path: text) -> bool:
        rt_opencv_imwrite(path, self.handle)

    fn drop():
        if self.owns_handle:
            rt_opencv_mat_free(self.handle)

# User-facing API
fn load_image(path: text) -> Mat:
    Mat.imread(path)
```

**Key Points**:
- RAII pattern (constructor + drop)
- Idiomatic Simple API
- Error handling
- Operator overloading

### Step 4: Build Integration

```bash
# Build the Rust wrapper
cd .build/rust/ffi_opencv
cargo build --release

# Or use Simple build system (future)
bin/simple build ffi opencv
```

## Directory Structure Template

```
your-library/
├── .build/rust/ffi_<library>/     # Tier 1: Rust wrapper
│   ├── Cargo.toml
│   ├── build.rs
│   ├── README.md
│   └── src/
│       └── lib.rs
│
├── src/lib/<library>/             # Tier 2 + 3: Simple
│   ├── ffi.spl                    # Tier 2: extern declarations
│   ├── mod.spl                    # Tier 3: User API
│   └── <modules>.spl              # Tier 3: Additional modules
│
├── src/lib/pure/                  # Pure Simple fallback
│   └── <library>_ffi.spl
│
└── test/lib/                      # Tests
    ├── <library>_spec.spl
    └── <library>_integration_spec.spl
```

## PyTorch Example (Complete)

See the complete PyTorch wrapper:

**Tier 1 (Rust)**:
- Location: `.build/rust/ffi_torch/`
- Files: `Cargo.toml`, `build.rs`, `src/lib.rs`
- Status: Prototype (stub implementation)

**Tier 2 (Simple SFFI)**:
- Location: `src/lib/torch/ffi.spl` (to be created)
- 16 FFI functions

**Tier 3 (Simple API)**:
- Location: `src/lib/torch/mod.spl` (to be created)
- Classes: `Tensor`
- Operations: zeros, ones, add, mul, matmul, relu, etc.

**Pure Simple Fallback**:
- Location: `src/lib/pure/torch_ffi.spl` (exists)
- 100% Pure Simple implementation

## Common Patterns

### Opaque Handle Pattern

```rust
// Tier 1 (Rust)
#[repr(C)]
pub struct SimpleLibraryObject {
    ptr: *mut c_void,  // Pointer to C++ object
    owns: bool,
}

impl Drop for SimpleLibraryObject {
    fn drop(&mut self) {
        if self.owns && !self.ptr.is_null() {
            unsafe { library_free(self.ptr); }
        }
    }
}
```

```simple
# Tier 2 (Simple SFFI)
extern type LibraryObjectHandle
extern fn rt_library_object_free(handle: LibraryObjectHandle)
```

```simple
# Tier 3 (Simple API)
class Object:
    handle: LibraryObjectHandle

    fn drop():
        rt_library_object_free(self.handle)
```

### Feature Detection Pattern

```simple
fn get_backend() -> text:
    if rt_library_available():
        "ffi"      # Use FFI backend
    else:
        "pure"     # Fall back to pure Simple

fn operation(x):
    if get_backend() == "ffi":
        operation_ffi(x)    # Fast FFI version
    else:
        operation_pure(x)   # Pure Simple version
```

### Error Handling Pattern

**Option 1: Boolean return**
```rust
#[no_mangle]
pub extern "C" fn simple_lib_write(path: *const c_char, data: *const u8, len: usize) -> bool {
    // Returns true on success, false on failure
}
```

**Option 2: Null on error**
```rust
#[no_mangle]
pub extern "C" fn simple_lib_read(path: *const c_char) -> *mut SimpleLibData {
    // Returns null pointer on error
}
```

**Option 3: Separate error getter**
```rust
#[no_mangle]
pub extern "C" fn simple_lib_get_last_error() -> *const c_char {
    // Returns error message
}
```

## System Dependencies

Document required system libraries in:

**Cargo.toml**:
```toml
[package.metadata.simple]
library = "opencv"
system-deps = ["libopencv >= 4.0"]
platforms = ["linux", "macos", "windows"]
```

**README.md**:
```markdown
## Prerequisites

**Ubuntu/Debian:**
```bash
sudo apt-get install libopencv-dev
```

**macOS:**
```bash
brew install opencv
```
```

## Testing

### Rust Unit Tests

```rust
#[cfg(test)]
mod tests {
    #[test]
    fn test_null_safety() {
        assert!(simple_lib_create(ptr::null()).is_null());
    }
}
```

### Simple Integration Tests

```simple
# test/lib/<library>_spec.spl
use lib.<library>.*

describe "Library FFI":
    it "is available":
        expect(library_available()).to_equal(true)

    it "creates objects":
        val obj = Object.create()
        expect(obj).to_not_be_nil()
```

## Checklist for New Library

- [ ] Create `.build/rust/ffi_<library>/` directory
- [ ] Write `Cargo.toml` with package metadata
- [ ] Write `build.rs` to find system library
- [ ] Implement `src/lib.rs` with FFI exports
- [ ] Create `src/lib/<library>/ffi.spl` with extern declarations
- [ ] Create `src/lib/<library>/mod.spl` with Simple API
- [ ] Write unit tests (Rust)
- [ ] Write integration tests (Simple)
- [ ] Document installation in README.md
- [ ] Add to Simple build system

## See Also

- **Design**: `doc/design/sffi_external_library_pattern.md`
- **PyTorch Example**: `doc/design/pytorch_thin_wrapper_design.md`
- **CLAUDE.md**: Lines 889-982
- **Skill**: `.claude/skills/sffi.md`
- **Prototype**: `.build/rust/ffi_torch/`

## Troubleshooting

### Library not found

```
error: linking with `cc` failed
rust-lld: error: unable to find library -ltorch
```

**Solution**: Set library path
```bash
export LIBTORCH=/opt/libtorch
export LD_LIBRARY_PATH=$LIBTORCH/lib:$LD_LIBRARY_PATH
```

### Symbol not found

```
undefined symbol: simple_lib_function
```

**Solution**: Check that function has `#[no_mangle]` and matches extern declaration

### Memory leaks

**Solution**: Ensure Drop trait is implemented for wrapper types

## Quick Start Command

```bash
# 1. Create directory structure
mkdir -p .build/rust/ffi_mylib/src
mkdir -p src/lib/mylib

# 2. Copy templates from PyTorch example
cp .build/rust/ffi_torch/Cargo.toml .build/rust/ffi_mylib/
cp .build/rust/ffi_torch/build.rs .build/rust/ffi_mylib/
cp .build/rust/ffi_torch/src/lib.rs .build/rust/ffi_mylib/src/

# 3. Edit files to replace "torch" with "mylib"

# 4. Build
cd .build/rust/ffi_mylib
cargo build --release
```
