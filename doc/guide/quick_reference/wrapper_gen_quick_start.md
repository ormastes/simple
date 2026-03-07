# Wrapper Generator Quick Start Guide

**Status**: Planned (Not Yet Implemented)
**See**: [Design Document](../design/cpp_wrapper_generator_design.md)

## Overview

The **Simple Wrapper Generator** (`simple wrapper-gen`) automates creation of FFI wrappers for external C++ libraries, generating all three tiers of the SFFI pattern from a simple specification file.

**What it generates**:
- ✅ Tier 1: Rust FFI wrapper (`.build/rust/ffi_<lib>/`)
- ✅ Tier 2: Simple SFFI bindings (`src/lib/<lib>/ffi.spl`)
- ✅ Tier 3: Simple API scaffold (`src/lib/<lib>/mod.spl`)

**Time savings**: ~8x faster than manual wrapping (4 hours → 30 minutes)

## Quick Example

### Step 1: Create Wrapper Spec

Create `mylib.wrapper_spec`:

```simple
wrapper_lib:
  name: mylib
  version: 1.0
  includes: ["mylib/core.h"]
  link: ["mylib"]

# Define opaque handle type
handle_type MyObject:
  cpp_type: "mylib::Object"
  doc: "Main object type"

# Define functions
fn create_object:
  cpp_fn: "mylib::create"
  params:
    - name: text
    - size: i64
  return: MyObject
  doc: "Create new object"

fn object_get_size:
  cpp_fn: "mylib::get_size"
  params:
    - obj: MyObject
  return: i64
  doc: "Get object size"

fn destroy_object:
  cpp_fn: "mylib::destroy"
  params:
    - obj: MyObject
  doc: "Free object"
```

### Step 2: Generate Wrappers

```bash
simple wrapper-gen mylib.wrapper_spec --all
```

**This generates**:

```
.build/rust/ffi_mylib/
├── Cargo.toml           # Package manifest
├── build.rs             # Build script
└── src/
    └── lib.rs           # Rust FFI wrapper

src/lib/mylib/
├── ffi.spl              # Simple SFFI bindings (Tier 2)
└── mod.spl              # Simple API scaffold (Tier 3)
```

### Step 3: Build Rust Wrapper

```bash
cd .build/rust/ffi_mylib
cargo build --release
```

### Step 4: Use in Simple

```simple
use lib.mylib.*

fn main():
    val obj = MyObject.create("test", 100)
    print "Size: {obj.get_size()}"
    # obj automatically freed when out of scope
```

## CLI Commands

### Generate All Tiers

```bash
# Generate everything
simple wrapper-gen spec.wrapper_spec --all

# Same as:
simple wrapper-gen spec.wrapper_spec --tier1 --tier2 --tier3
```

### Generate Specific Tiers

```bash
# Only Rust FFI wrapper (Tier 1)
simple wrapper-gen spec.wrapper_spec --tier1

# Only Simple SFFI bindings (Tier 2)
simple wrapper-gen spec.wrapper_spec --tier2

# Only Simple API scaffold (Tier 3)
simple wrapper-gen spec.wrapper_spec --tier3
```

### Custom Output Locations

```bash
simple wrapper-gen spec.wrapper_spec \
  --output-rust .build/rust/ffi_custom \
  --output-sffi src/lib/custom/ffi.spl \
  --output-api src/lib/custom/mod.spl
```

### Validation & Preview

```bash
# Validate spec without generating
simple wrapper-gen spec.wrapper_spec --check

# Preview generated code (dry run)
simple wrapper-gen spec.wrapper_spec --dry-run

# Verbose output
simple wrapper-gen spec.wrapper_spec --verbose
```

### Header Parsing (Future)

```bash
# Generate from C++ headers directly
simple wrapper-gen --headers /usr/include/mylib/core.h \
                    --library mylib \
                    --filter 'mylib::*'
```

## Spec Format

### Basic Structure

```simple
wrapper_lib:
  name: <library_name>
  version: <version>
  includes: [<header_files>]
  link: [<link_libraries>]
  pkg_config: <pkg_config_name>  # Optional

# Opaque handle types
handle_type <TypeName>:
  cpp_type: "<C++_type>"
  doc: "<description>"
  thread_safe: <true|false>  # Optional

# Free functions
fn <function_name>:
  cpp_fn: "<C++_function_name>"
  params:
    - <param_name>: <type>
    - <param_name>: <type> (<ownership>)
  return: <type>
  return_ownership: <owned|borrowed>  # Optional
  thread_safe: <true|false>           # Optional
  doc: "<description>"

# Classes (for methods)
class <ClassName>:
  methods:
    fn <method_name>:
      cpp_fn: "<C++_method_name>"
      params: [...]
      return: <type>
      mutability: <const|mut>
```

### Type Mappings

| Simple Type | Rust FFI Type | C++ Type |
|-------------|---------------|----------|
| `text` | `*const c_char, usize` | `const char*, size_t` |
| `i64` | `i64` | `int64_t` |
| `i32` | `i32` | `int32_t` |
| `f64` | `f64` | `double` |
| `bool` | `u8` | `bool` |
| `[i64]` | `*const i64, usize` | `const int64_t*, size_t` |
| `[f64]` | `*const f64, usize` | `const double*, size_t` |
| `MyHandle` | `*mut SimpleMyHandle` | `mylib::MyType*` |

### Ownership Annotations

**For parameters**:
```simple
fn process:
  params:
    - obj: MyObject (borrow)    # Borrowed (const reference)
    - data: MyObject (mut)      # Mutable borrow (mut reference)
    - owned: MyObject (consume) # Consumes the object
```

**For return values**:
```simple
fn create:
  return: MyObject
  return_ownership: owned       # Caller owns, must free

fn get_ref:
  return: MyObject
  return_ownership: borrowed    # Borrowed, don't free
```

### Safety Annotations

```simple
fn my_function:
  safety:
    null_check: true            # Check for null return
    thread_safe: true           # Can call from multiple threads
    exception_safe: false       # May throw C++ exceptions
```

## Generated Code Examples

### Tier 1: Rust FFI Wrapper

**Generated `.build/rust/ffi_mylib/src/lib.rs`**:

```rust
// Auto-generated by Simple wrapper-gen - DO NOT EDIT

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_void};

#[link(name = "mylib")]
extern "C" {
    fn mylib_create(name: *const c_char, size: i64) -> *mut c_void;
    fn mylib_get_size(obj: *mut c_void) -> i64;
    fn mylib_destroy(obj: *mut c_void);
}

pub struct SimpleMyObject {
    ptr: *mut c_void,
}

#[no_mangle]
pub extern "C" fn simple_mylib_create_object(
    name: *const c_char,
    name_len: usize,
    size: i64
) -> *mut SimpleMyObject {
    unsafe {
        let name_str = std::str::from_utf8_unchecked(
            std::slice::from_raw_parts(name, name_len)
        );
        let c_name = CString::new(name_str).unwrap();
        let ptr = mylib_create(c_name.as_ptr(), size);
        Box::into_raw(Box::new(SimpleMyObject { ptr }))
    }
}

#[no_mangle]
pub extern "C" fn simple_mylib_object_get_size(
    obj: *mut SimpleMyObject
) -> i64 {
    unsafe {
        mylib_get_size((*obj).ptr)
    }
}

#[no_mangle]
pub extern "C" fn simple_mylib_destroy_object(
    obj: *mut SimpleMyObject
) {
    unsafe {
        if !obj.is_null() {
            mylib_destroy((*obj).ptr);
            drop(Box::from_raw(obj));
        }
    }
}
```

### Tier 2: Simple SFFI Bindings

**Generated `src/lib/mylib/ffi.spl`**:

```simple
# mylib SFFI Bindings (Tier 2)
# Auto-generated by wrapper-gen - DO NOT EDIT

# ============================================================================
# Opaque Handle Types
# ============================================================================

# Main object type
extern type MyObjectHandle

# ============================================================================
# Functions
# ============================================================================

# Create new object
extern fn rt_mylib_create_object(name: text, size: i64) -> MyObjectHandle

# Get object size
extern fn rt_mylib_object_get_size(obj: MyObjectHandle) -> i64

# Free object
extern fn rt_mylib_destroy_object(obj: MyObjectHandle)
```

### Tier 3: Simple API Scaffold

**Generated `src/lib/mylib/mod.spl`**:

```simple
# mylib Simple API (Tier 3)
# Generated scaffold - CUSTOMIZE AS NEEDED

use lib.mylib.ffi.*

# ============================================================================
# Main object type
# ============================================================================

class MyObject:
    handle: MyObjectHandle
    owns_handle: bool

    # Constructor (customize as needed)
    fn init(handle: MyObjectHandle):
        self.handle = handle
        self.owns_handle = true

    # Destructor (automatic cleanup)
    fn drop():
        if self.owns_handle:
            rt_mylib_destroy_object(self.handle)

    # Static factory method
    # TODO: Customize parameters and documentation
    static fn create(name: text, size: i64) -> MyObject:
        val handle = rt_mylib_create_object(name, size)
        MyObject(handle: handle, owns_handle: true)

    # Instance method
    # TODO: Customize return type and error handling
    fn get_size() -> i64:
        rt_mylib_object_get_size(self.handle)

# ============================================================================
# Module-level functions (TODO: Add as needed)
# ============================================================================

# TODO: Add convenience functions
# fn mylib_version() -> text:
#     rt_mylib_version()
```

## Real-World Example: PyTorch

### Original Manual Wrapper

**Manual effort**: ~4 hours
**Code**: 550 lines Rust + 666 lines Simple = 1,216 lines total

### With Wrapper Generator

**Spec file** (50 lines):

```simple
wrapper_lib:
  name: torch
  version: 2.0
  includes: ["torch/torch.h"]
  link: ["torch", "c10"]

handle_type TorchTensor:
  cpp_type: "torch::Tensor"

fn tensor_zeros:
  cpp_fn: "torch::zeros"
  params: [dims: [i64]]
  return: TorchTensor

fn tensor_add:
  cpp_fn: "torch::add"
  params:
    - a: TorchTensor (borrow)
    - b: TorchTensor (borrow)
  return: TorchTensor
  return_ownership: owned

fn tensor_free:
  cpp_fn: "torch::tensor_free"
  params:
    - tensor: TorchTensor (consume)
```

**Generated**: All 1,216 lines of code automatically
**Time**: ~30 minutes (spec writing + customization)
**Improvement**: **8x faster**

## Best Practices

### 1. Start Simple

**First iteration**:
- Only wrap core functions
- Use opaque handles
- Defer complex types

**Example**:
```simple
# Good first iteration
handle_type MyObject:
  cpp_type: "mylib::Object"

fn create: ...
fn destroy: ...
```

### 2. Add Safety Annotations

**Always specify ownership**:
```simple
fn process:
  params:
    - input: MyObject (borrow)    # Clear: doesn't consume
    - output: MyObject (consume)  # Clear: takes ownership
  return: MyObject
  return_ownership: owned         # Clear: caller must free
```

### 3. Customize Tier 3

**Don't use generated API as-is**:
- Add error handling
- Add convenience methods
- Improve documentation
- Add operator overloads

**Example**:
```simple
# Generated (basic)
fn get_size() -> i64:
    rt_mylib_object_get_size(self.handle)

# Customized (better)
fn size() -> i64:
    """Get the object size in bytes."""
    val result = rt_mylib_object_get_size(self.handle)
    if result < 0:
        panic("Invalid object handle")
    result
```

### 4. Use Comments for Manual Work

The generator adds `# TODO:` comments for areas needing customization:

```simple
# TODO: Add error handling
# TODO: Customize parameters
# TODO: Add documentation
```

Search for these and fill them in.

## Troubleshooting

### Spec Validation Errors

**Error**: `Unknown type: MyCustomType`

**Solution**: Define the type in the spec:
```simple
handle_type MyCustomType:
  cpp_type: "mylib::CustomType"
```

### Build Failures

**Error**: `library not found for -lmylib`

**Solution**: Ensure library is in linker path:
```bash
export LD_LIBRARY_PATH=/usr/local/lib:$LD_LIBRARY_PATH
```

Or add to `build.rs`:
```rust
println!("cargo:rustc-link-search=/usr/local/lib");
```

### Type Mismatches

**Error**: `expected *const c_char, found text`

**Solution**: Check type mappings in spec. Use correct Simple type:
- `text` for strings
- `i64` for integers
- `[i64]` for integer arrays

## Advanced Features

### Custom Type Converters

**For complex types**:

```simple
type_mapping:
  TorchDevice:
    simple: text
    rust: "CString"
    cpp: "torch::Device"
    converter: "device_from_string"
```

### Platform-Specific Builds

```simple
platforms:
  linux:
    link: ["mylib", "pthread", "dl"]
  macos:
    link: ["mylib", "pthread"]
    frameworks: ["CoreFoundation"]
  windows:
    link: ["mylib.lib", "ws2_32.lib"]
```

### Error Handling

```simple
error_handling:
  mode: return_code     # or exceptions, or none
  null_is_error: true   # Null return = error
```

## Next Steps

After generating wrappers:

1. **Review generated code** - Check for correctness
2. **Customize Tier 3** - Add error handling, docs, convenience methods
3. **Write tests** - Test all generated functions
4. **Document usage** - Add examples and guides
5. **Iterate** - Refine spec based on usage

## See Also

- [Complete Design Document](../design/cpp_wrapper_generator_design.md)
- [SFFI External Library Pattern](../design/sffi_external_library_pattern.md)
- [SFFI Quick Start Guide](sffi_external_libraries_quick_start.md)
- [Research Report](../report/cpp_wrapper_generator_research_2026-02-08.md)

## Status Note

⚠️ **This tool is not yet implemented**. This guide describes the planned functionality based on the complete design document. See the [design doc](../design/cpp_wrapper_generator_design.md) for implementation plan.
