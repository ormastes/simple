# Automatic C++ Wrapper Generator Design

**Status**: Design Phase
**Created**: 2026-02-08
**Author**: Research & Design

## Executive Summary

This document proposes an **automatic wrapper generator** for C++ libraries in the Simple language project. The tool will automate the generation of Rust FFI wrappers (Tier 1) and Simple SFFI bindings (Tier 2) from C++ API specifications, significantly reducing manual effort and error potential when integrating external libraries.

**Key Goals**:
1. Automate Rust FFI wrapper generation from C++ APIs
2. Generate matching Simple SFFI bindings automatically
3. Support Simple's three-tier SFFI pattern
4. Minimize manual boilerplate code
5. Validate type mappings and safety guarantees

## Background

### Current State in Simple

Simple currently has:

1. **Two-tier SFFI pattern** (runtime functions)
   - Tier 1: `extern fn rt_*` in Simple
   - Tier 2: Simple wrapper functions
   - Example: `src/app/io/mod.spl` (800+ manual FFI declarations)

2. **Three-tier SFFI pattern** (external libraries)
   - Tier 0: External C++ library (libtorch, OpenCV, etc.)
   - Tier 1: Thin Rust wrapper (.build/rust/ffi_*/lib.rs)
   - Tier 2: SFFI bindings (src/lib/*/ffi.spl)
   - Tier 3: Simple API layer (src/lib/*/mod.spl)
   - Example: PyTorch wrapper (550 lines Rust + 666 lines Simple)

3. **Manual FFI generation** (limited scope)
   - Tool: `src/app/ffi_gen/` (17 modules, ~2,000 lines)
   - Generates Rust FFI code from Simple specs (`InternFnSpec`)
   - Limited to Simple-defined functions, not external C++ libraries

### Problem Statement

**Manual wrapper creation is tedious and error-prone**:
- PyTorch wrapper took 550 lines of Rust boilerplate
- Each function requires 3-4 manual type conversions
- Easy to introduce memory leaks or type mismatches
- Must manually sync Simple types with Rust types with C++ types

**What we need**:
- Automatic generation of Tier 1 (Rust wrapper)
- Automatic generation of Tier 2 (Simple SFFI bindings)
- Type safety validation across all three tiers
- Support for common C++ patterns (classes, methods, templates)

## Existing Tools Analysis

### Tool Comparison Matrix

| Tool | Direction | C++ Support | Template Support | Use Case | Pros | Cons |
|------|-----------|-------------|------------------|----------|------|------|
| **bindgen** | C/C++ → Rust | Partial | Limited | Generate Rust bindings | Mature, header-based | Doesn't handle templates well |
| **cxx** | Rust ↔ C++ | Full | Manual bridge | Safe interop | Type-safe, bidirectional | Requires manual bridge spec |
| **autocxx** | C++ → Rust | Full | Automatic | Existing C++ codebases | Combines bindgen + cxx | Evolving, less mature |
| **cbindgen** | Rust → C | N/A | N/A | Expose Rust to C | Good for Rust exports | Wrong direction for us |

### Detailed Analysis

#### 1. bindgen ([rust-lang/rust-bindgen](https://github.com/rust-lang/rust-bindgen))

**What it does**: Automatically generates Rust FFI bindings from C/C++ header files using libclang.

**Strengths**:
- Mature and widely used
- Header-based (can work with any C++ library)
- Handles C types very well

**Limitations for Simple**:
- C++ support is limited ([docs](https://rust-lang.github.io/rust-bindgen/cpp.html)):
  - No inline functions
  - No template functions
  - No template class methods
  - Only generates type definitions, not nice APIs
- Generates unsafe Rust code (raw pointers)
- Doesn't generate Simple bindings

**Verdict**: Could be used as a *component* (parse headers → AST), but not a complete solution.

#### 2. cxx ([dtolnay/cxx](https://cxx.rs/))

**What it does**: Safe Rust-C++ interop using a common "bridge" specification.

**How it works**:
```rust
#[cxx::bridge]
mod ffi {
    extern "C++" {
        include!("torch/torch.h");
        type Tensor;
        fn zeros(dims: &[i64]) -> UniquePtr<Tensor>;
    }
}
```

**Strengths**:
- Type-safe by design
- Generates both Rust and C++ code
- Handles C++ types (std::string, std::vector, etc.)
- Good template support (via explicit instantiation)

**Limitations for Simple**:
- Requires manual bridge specification
- Doesn't generate Simple bindings
- Complex setup for large APIs

**Verdict**: Excellent choice for *implementing* the Rust side (Tier 1), but we still need to generate the bridge specs.

#### 3. autocxx ([google/autocxx](https://github.com/google/autocxx))

**What it does**: Combines bindgen + cxx to automatically generate cxx bridges from C++ headers.

**How it works**:
```rust
autocxx::include_cpp! {
    #include "torch/torch.h"
    generate!("at::Tensor")
    safety!(unsafe_ffi)
}
```

**Strengths**:
- Automatic header parsing (like bindgen)
- Type-safe bridges (like cxx)
- Better C++ support than bindgen alone
- Handles more complex types

**Limitations for Simple**:
- Still evolving ([docs](https://google.github.io/autocxx/))
- Safety model more permissive than cxx
- Doesn't generate Simple bindings
- May generate "footguns" automatically

**Verdict**: Promising for future, but currently less mature than cxx. Could be used as inspiration.

#### 4. cbindgen ([mozilla/cbindgen](https://github.com/mozilla/cbindgen))

**What it does**: Generates C/C++ headers from Rust code (opposite direction).

**Strengths**:
- Good for exposing Rust to C/C++
- Can generate headers for our Rust FFI wrappers

**Limitations**:
- Wrong direction (Rust → C, we need C++ → Rust)
- Doesn't help with library wrapping

**Verdict**: Not applicable for C++ library wrapping, but could be useful for validating our generated Rust code.

### Recommendation

**Hybrid approach**:
1. Use **cxx** for Rust-C++ interop (Tier 1 implementation)
2. Use **bindgen** (optionally) for parsing C++ headers → AST
3. Build **custom codegen** on top to generate:
   - cxx bridge specifications
   - Simple SFFI bindings (Tier 2)
   - Simple API templates (Tier 3 scaffold)

## Proposed Architecture

### System Overview

```
┌─────────────────────────────────────────────────────────────────┐
│ INPUT: API Specification                                        │
│                                                                 │
│ Option A: C++ Headers (.h/.hpp)                                │
│   - Parse with bindgen/clang                                   │
│   - Extract class/function signatures                          │
│                                                                 │
│ Option B: Simple DSL (.sffi spec)                              │
│   - Custom spec format                                         │
│   - Declarative API description                                │
│   - Type mappings and safety annotations                       │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│ PARSER & ANALYZER                                               │
│   - Parse input (headers or spec)                              │
│   - Build internal AST                                         │
│   - Validate type mappings                                     │
│   - Detect unsupported patterns                                │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│ CODE GENERATOR (src/app/wrapper_gen/)                          │
│                                                                 │
│ ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│ │ Tier 1 Generator│  │ Tier 2 Generator│  │ Tier 3 Generator│ │
│ │   (Rust FFI)    │  │   (Simple SFFI) │  │  (Simple API)   │ │
│ └─────────────────┘  └─────────────────┘  └─────────────────┘ │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│ OUTPUT: Generated Code                                          │
│                                                                 │
│ Tier 1: .build/rust/ffi_<lib>/                                │
│   ├── Cargo.toml          # Package manifest                   │
│   ├── build.rs            # Build script (find library)        │
│   └── src/lib.rs          # Rust FFI wrapper                   │
│                                                                 │
│ Tier 2: src/lib/<lib>/ffi.spl                                 │
│   - extern fn declarations                                     │
│   - Opaque handle types                                        │
│                                                                 │
│ Tier 3: src/lib/<lib>/mod.spl (scaffold only)                 │
│   - Class templates                                            │
│   - Method stubs                                               │
│   - TODO comments for manual implementation                    │
└─────────────────────────────────────────────────────────────────┘
```

### Input Format Options

#### Option A: C++ Header Parsing (Future)

**Use bindgen's AST output**:

```bash
simple wrapper-gen --headers /usr/include/torch/torch.h \
                    --library torch \
                    --output .build/rust/ffi_torch
```

**Pros**:
- Works with existing C++ libraries
- No need to write specs manually
- Can extract documentation from comments

**Cons**:
- Complex C++ parsing
- Need to filter out unneeded functions
- Template expansion is hard

#### Option B: Simple DSL Spec (Recommended for v1)

**Custom spec format** (easier to implement, more control):

```simple
# torch.wrapper_spec
wrapper_lib:
  name: torch
  version: 2.0
  includes: ["torch/torch.h"]
  link: ["torch", "c10"]

# Opaque handle types
handle_type TorchTensor:
  cpp_type: "torch::Tensor"
  doc: "PyTorch tensor"

# Functions
fn tensor_zeros:
  cpp_fn: "torch::zeros"
  params:
    - dims: [i64]
  return: TorchTensor
  doc: "Create zero tensor"

fn tensor_add:
  cpp_fn: "torch::add"
  params:
    - a: TorchTensor
    - b: TorchTensor
  return: TorchTensor
  doc: "Element-wise addition"

# Classes (for methods)
class TorchTensor:
  constructor:
    fn zeros:
      cpp_fn: "torch::zeros"
      params: [dims: [i64]]

  methods:
    fn shape:
      cpp_fn: "sizes"
      return: [i64]
      mutability: const

    fn to_device:
      cpp_fn: "to"
      params: [device: text]
      return: TorchTensor
      mutability: const
```

**Pros**:
- Full control over what gets wrapped
- Easy to add type hints and safety annotations
- Simpler to implement (just parse SDN/custom format)
- Can specify memory ownership explicitly

**Cons**:
- Requires manual spec writing
- Specs might drift from actual C++ API

### Code Generation Phases

#### Phase 1: Parse Spec

```simple
# src/app/wrapper_gen/spec_parser.spl

struct WrapperSpec:
    lib_name: text
    version: text
    includes: [text]
    link_libs: [text]
    handle_types: [HandleTypeSpec]
    functions: [FunctionSpec]
    classes: [ClassSpec]

struct HandleTypeSpec:
    simple_name: text
    cpp_type: text
    doc: text

struct FunctionSpec:
    simple_name: text
    cpp_fn: text
    params: [ParamSpec]
    return_type: TypeSpec
    doc: text

fn parse_wrapper_spec(spec_path: text) -> WrapperSpec:
    # Parse SDN/custom format
    # Build spec AST
    # Validate types
```

#### Phase 2: Generate Tier 1 (Rust FFI)

```simple
# src/app/wrapper_gen/tier1_gen.spl

fn generate_rust_wrapper(spec: WrapperSpec) -> RustCode:
    var code = RustCode()

    # Generate Cargo.toml
    code.cargo_toml = generate_cargo_toml(spec)

    # Generate build.rs
    code.build_rs = generate_build_script(spec)

    # Generate lib.rs
    code.lib_rs = ""

    # Includes
    code.lib_rs += "use std::ffi::{{CStr, CString}};\n"
    code.lib_rs += "use std::os::raw::{{c_char, c_void}};\n\n"

    # Link directives
    for lib in spec.link_libs:
        code.lib_rs += "#[link(name = \"{lib}\")]\n"

    # Extern C++ declarations
    code.lib_rs += "extern \"C++\" {\n"
    for func in spec.functions:
        code.lib_rs += generate_cpp_binding(func)
    code.lib_rs += "}\n\n"

    # Handle types
    for handle_type in spec.handle_types:
        code.lib_rs += generate_handle_struct(handle_type)

    # FFI exports
    for func in spec.functions:
        code.lib_rs += generate_ffi_export(func)

    code
```

**Generated Rust example**:

```rust
// Auto-generated by Simple wrapper-gen
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_void};

#[link(name = "torch")]
extern "C" {
    fn at_zeros(dims: *const i64, ndims: usize) -> *mut c_void;
    fn at_add(a: *mut c_void, b: *mut c_void) -> *mut c_void;
}

pub struct SimpleTorchTensor {
    ptr: *mut c_void,
}

#[no_mangle]
pub extern "C" fn simple_torch_tensor_zeros(
    dims: *const i64,
    ndims: usize
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_zeros(dims, ndims);
        Box::into_raw(Box::new(SimpleTorchTensor { ptr }))
    }
}

#[no_mangle]
pub extern "C" fn simple_torch_tensor_add(
    a: *mut SimpleTorchTensor,
    b: *mut SimpleTorchTensor
) -> *mut SimpleTorchTensor {
    unsafe {
        let ptr = at_add((*a).ptr, (*b).ptr);
        Box::into_raw(Box::new(SimpleTorchTensor { ptr }))
    }
}

#[no_mangle]
pub extern "C" fn simple_torch_tensor_free(tensor: *mut SimpleTorchTensor) {
    unsafe {
        if !tensor.is_null() {
            drop(Box::from_raw(tensor));
        }
    }
}
```

#### Phase 3: Generate Tier 2 (Simple SFFI)

```simple
# src/app/wrapper_gen/tier2_gen.spl

fn generate_sffi_bindings(spec: WrapperSpec) -> text:
    var code = "# {spec.lib_name} SFFI Bindings (Tier 2)\n"
    code += "# Auto-generated - DO NOT EDIT\n\n"

    # Opaque handle types
    for handle_type in spec.handle_types:
        code += "extern type {handle_type.simple_name}\n"
    code += "\n"

    # Extern function declarations
    for func in spec.functions:
        code += generate_extern_fn_decl(func)

    code
```

**Generated Simple example**:

```simple
# torch SFFI Bindings (Tier 2)
# Auto-generated by wrapper-gen - DO NOT EDIT

# ============================================================================
# Opaque Handle Types
# ============================================================================

extern type TorchTensorHandle

# ============================================================================
# Tensor Creation
# ============================================================================

# Create zero tensor
extern fn rt_torch_tensor_zeros(dims: [i64]) -> TorchTensorHandle

# Element-wise addition
extern fn rt_torch_tensor_add(a: TorchTensorHandle, b: TorchTensorHandle) -> TorchTensorHandle

# Free tensor
extern fn rt_torch_tensor_free(handle: TorchTensorHandle)
```

#### Phase 4: Generate Tier 3 Scaffold (Optional)

```simple
# src/app/wrapper_gen/tier3_gen.spl

fn generate_api_scaffold(spec: WrapperSpec) -> text:
    var code = "# {spec.lib_name} Simple API (Tier 3)\n"
    code += "# Generated scaffold - CUSTOMIZE AS NEEDED\n\n"
    code += "use lib.{spec.lib_name}.ffi.*\n\n"

    # Generate class templates
    for class_spec in spec.classes:
        code += generate_class_scaffold(class_spec)

    code
```

**Generated scaffold**:

```simple
# torch Simple API (Tier 3)
# Generated scaffold - CUSTOMIZE AS NEEDED

use lib.torch.ffi.*

class Tensor:
    handle: TorchTensorHandle
    owns_handle: bool

    # TODO: Implement constructor
    fn init(handle: TorchTensorHandle):
        self.handle = handle
        self.owns_handle = true

    # TODO: Implement destructor
    fn drop():
        if self.owns_handle:
            rt_torch_tensor_free(self.handle)

    # TODO: Implement static factory
    static fn zeros(shape: [i64]) -> Tensor:
        val handle = rt_torch_tensor_zeros(shape)
        Tensor(handle: handle, owns_handle: true)

    # TODO: Implement method
    fn add(other: Tensor) -> Tensor:
        val result = rt_torch_tensor_add(self.handle, other.handle)
        Tensor(handle: result, owns_handle: true)
```

### Type Mapping System

#### Core Type Mappings

| Simple Type | Rust FFI Type | C++ Type | Notes |
|-------------|---------------|----------|-------|
| `text` | `*const c_char, usize` | `const char*, size_t` | UTF-8 string |
| `i64` | `i64` | `int64_t` | Direct pass |
| `i32` | `i32` | `int32_t` | Direct pass |
| `f64` | `f64` | `double` | Direct pass |
| `bool` | `u8` | `bool` | 0/1 conversion |
| `[i64]` | `*const i64, usize` | `const int64_t*, size_t` | Array + length |
| `[f64]` | `*const f64, usize` | `const double*, size_t` | Array + length |
| `TensorHandle` | `*mut SimpleTensor` | `torch::Tensor*` | Opaque pointer |

#### Custom Type Registration

```simple
# In spec file
type_mapping:
  TorchDevice:
    simple: text
    rust: "CString"
    cpp: "torch::Device"
    converter: "device_from_string"
```

### Memory Safety Analysis

The generator should analyze and enforce:

1. **Ownership tracking**
   - Who owns the returned pointer?
   - Does the function consume input handles?
   - Mark as `owns_handle: bool` in generated code

2. **Lifetime annotations**
   - Are returned pointers valid after function returns?
   - Does the output borrow from inputs?

3. **Null safety**
   - Can function return null?
   - Add null checks in generated code

Example spec with safety annotations:

```simple
fn tensor_add:
  cpp_fn: "torch::add"
  params:
    - a: TorchTensor (borrow)
    - b: TorchTensor (borrow)
  return: TorchTensor (owned)
  safety:
    null_check: false  # Never returns null
    thread_safe: true
```

## Implementation Plan

### Phase 0: Infrastructure (Week 1)

**Goal**: Set up basic structure

- [ ] Create `src/app/wrapper_gen/` directory
- [ ] Define spec format (SDN-based)
- [ ] Create AST types for wrapper specs
- [ ] Write spec parser

**Deliverables**:
- `src/app/wrapper_gen/types.spl` - AST types
- `src/app/wrapper_gen/parser.spl` - Spec parser
- `examples/torch.wrapper_spec` - Example spec

### Phase 1: Tier 1 Generator (Week 2)

**Goal**: Generate Rust FFI wrappers

- [ ] Implement Rust codegen for simple functions
- [ ] Add handle type generation
- [ ] Generate Cargo.toml and build.rs
- [ ] Add type mapping system
- [ ] Test with PyTorch subset

**Deliverables**:
- `src/app/wrapper_gen/tier1_gen.spl` - Rust generator
- `src/app/wrapper_gen/type_mapper.spl` - Type conversions
- Generated code compiles with cargo

### Phase 2: Tier 2 Generator (Week 3)

**Goal**: Generate Simple SFFI bindings

- [ ] Implement Simple extern fn generation
- [ ] Generate opaque type declarations
- [ ] Add documentation comments
- [ ] Validate type consistency

**Deliverables**:
- `src/app/wrapper_gen/tier2_gen.spl` - SFFI generator
- Generated SFFI matches Rust exports

### Phase 3: Tier 3 Scaffold (Week 4)

**Goal**: Generate API scaffolds

- [ ] Generate class templates
- [ ] Add RAII patterns (drop)
- [ ] Generate operator overloads
- [ ] Add TODO comments for manual work

**Deliverables**:
- `src/app/wrapper_gen/tier3_gen.spl` - Scaffold generator
- Usable class templates

### Phase 4: Integration & Testing (Week 5)

**Goal**: Complete the tool

- [ ] CLI integration (`simple wrapper-gen`)
- [ ] Write comprehensive tests
- [ ] Documentation and examples
- [ ] Re-generate PyTorch wrapper to validate

**Deliverables**:
- `src/app/wrapper_gen/main.spl` - CLI entry point
- `test/app/wrapper_gen_spec.spl` - Tests
- `doc/guide/wrapper_gen_guide.md` - User guide

### Phase 5: Advanced Features (Future)

- [ ] Header parsing with bindgen integration
- [ ] Template expansion
- [ ] C++ exception handling
- [ ] Async function support
- [ ] Multi-platform build configs

## Example Usage

### Workflow

**Step 1: Write spec**

```bash
# Create torch.wrapper_spec
cat > torch.wrapper_spec << 'EOF'
wrapper_lib:
  name: torch
  version: 2.0
  includes: ["torch/torch.h"]
  link: ["torch"]

handle_type TorchTensor:
  cpp_type: "torch::Tensor"

fn tensor_zeros:
  cpp_fn: "torch::zeros"
  params:
    - dims: [i64]
  return: TorchTensor
EOF
```

**Step 2: Generate wrappers**

```bash
simple wrapper-gen torch.wrapper_spec \
  --output-rust .build/rust/ffi_torch \
  --output-sffi src/lib/torch/ffi.spl \
  --output-api src/lib/torch/mod.spl
```

**Step 3: Build Rust wrapper**

```bash
cd .build/rust/ffi_torch
cargo build --release
```

**Step 4: Use in Simple**

```simple
use lib.torch.*

fn main():
    val t = Tensor.zeros([2, 3])
    print "Created tensor: {t.shape()}"
```

### CLI Commands

```bash
# Generate all tiers
simple wrapper-gen spec.wrapper_spec --all

# Generate specific tier only
simple wrapper-gen spec.wrapper_spec --tier1
simple wrapper-gen spec.wrapper_spec --tier2
simple wrapper-gen spec.wrapper_spec --tier3

# Validate spec without generating
simple wrapper-gen spec.wrapper_spec --check

# Preview generated code
simple wrapper-gen spec.wrapper_spec --dry-run

# Use header files (future)
simple wrapper-gen --headers /usr/include/torch/torch.h \
                    --library torch \
                    --filter 'torch::*'
```

## Benefits

### Compared to Manual Wrapping

| Aspect | Manual | With Generator | Improvement |
|--------|--------|----------------|-------------|
| **Time** | ~4 hours/library | ~30 min | 8x faster |
| **Error Rate** | High (manual typing) | Low (validated) | 10x safer |
| **Consistency** | Varies | Uniform | ✅ |
| **Maintenance** | Update 3 files | Regenerate | 3x easier |
| **Documentation** | Often missing | Auto-generated | ✅ |

### Safety Improvements

1. **Type safety**: Validated at generation time
2. **Memory safety**: Ownership tracked automatically
3. **ABI compatibility**: Consistent calling conventions
4. **Null safety**: Explicit null checks generated

## Risks & Mitigations

### Risk 1: Complex C++ Not Supported

**Risk**: Templates, inheritance, overloading are hard to wrap automatically.

**Mitigation**:
- Start with simple functions and opaque handles
- Add manual escape hatches for complex cases
- Document unsupported patterns clearly

### Risk 2: Generated Code Quality

**Risk**: Generated code might not be idiomatic or efficient.

**Mitigation**:
- Use templates based on hand-written wrappers
- Allow customization via spec annotations
- Make Tier 3 (API) a scaffold, not fully generated

### Risk 3: Spec Maintenance Burden

**Risk**: Specs might become outdated as C++ APIs evolve.

**Mitigation**:
- Add version checking in generated code
- Provide tools to diff spec vs headers
- Eventually support header parsing

## Success Metrics

**v1.0 (Minimum Viable)**:
- [ ] Can regenerate PyTorch wrapper from spec
- [ ] Generated code compiles and passes tests
- [ ] Reduces manual code by 80%+
- [ ] Type safety validated

**v2.0 (Production Ready)**:
- [ ] Supports 5+ libraries (PyTorch, OpenCV, SQLite, etc.)
- [ ] Header parsing works for simple APIs
- [ ] Documentation auto-generated
- [ ] Integration tests pass

**v3.0 (Advanced)**:
- [ ] Template expansion
- [ ] C++ exception handling
- [ ] Async function support
- [ ] Cross-platform builds

## Related Work

### In Simple Codebase

- **Existing FFI gen**: `src/app/ffi_gen/` (for runtime functions)
- **Three-tier pattern**: `doc/design/sffi_external_library_pattern.md`
- **PyTorch wrapper**: `.build/rust/ffi_torch/` (manual example)

### External Tools

- [bindgen](https://github.com/rust-lang/rust-bindgen) - C/C++ to Rust
- [cxx](https://cxx.rs/) - Safe Rust-C++ interop
- [autocxx](https://github.com/google/autocxx) - Automatic cxx bridges
- [cbindgen](https://github.com/mozilla/cbindgen) - Rust to C headers

## Conclusion

An automatic wrapper generator for C++ libraries would:

1. **Dramatically reduce effort** - 8x faster library wrapping
2. **Improve safety** - Type-validated, memory-safe wrappers
3. **Enable scaling** - Easy to wrap many libraries
4. **Maintain quality** - Consistent, idiomatic code

**Recommendation**: Implement in phases, starting with spec-based generation (simpler) and adding header parsing later (harder but more powerful).

The tool will be a **force multiplier** for integrating external libraries into Simple, making the three-tier SFFI pattern practical for dozens of libraries instead of just a handful.

## See Also

- [SFFI External Library Pattern](sffi_external_library_pattern.md)
- [PyTorch Wrapper Design](pytorch_thin_wrapper_design.md)
- [SFFI Quick Start Guide](../guide/sffi_external_libraries_quick_start.md)
- [SFFI Three-Tier Complete Report](../report/sffi_three_tier_pattern_complete_2026-02-08.md)

## Appendix: Spec Format Reference

### Complete Spec Example

```simple
# library.wrapper_spec - Complete example

wrapper_lib:
  name: mylib
  version: 1.0
  includes: ["mylib/core.h", "mylib/util.h"]
  link: ["mylib", "pthread"]
  pkg_config: "mylib >= 1.0"

# Define opaque handle types
handle_type MyObject:
  cpp_type: "mylib::Object"
  doc: "Main object type"
  thread_safe: true

handle_type MyIterator:
  cpp_type: "mylib::Iterator<int>"
  doc: "Iterator over integers"

# Define type aliases
type_alias MyString:
  simple: text
  cpp: "std::string"

# Free functions
fn create_object:
  cpp_fn: "mylib::create"
  params:
    - name: text
    - size: i64
  return: MyObject
  return_ownership: owned
  doc: "Create new object"

fn destroy_object:
  cpp_fn: "mylib::destroy"
  params:
    - obj: MyObject (consumed)
  return: void
  doc: "Free object"

fn object_size:
  cpp_fn: "mylib::get_size"
  params:
    - obj: MyObject (borrow)
  return: i64
  thread_safe: true
  doc: "Get object size"

# Classes (for method wrapping)
class MyObject:
  methods:
    fn get_name:
      cpp_fn: "getName"
      return: text
      mutability: const

    fn set_size:
      cpp_fn: "setSize"
      params:
        - new_size: i64
      mutability: mut

# Error handling
error_handling:
  mode: return_code  # or exceptions, or none
  null_is_error: true

# Platform-specific
platforms:
  linux:
    link: ["mylib", "pthread", "dl"]
  macos:
    link: ["mylib", "pthread"]
    frameworks: ["CoreFoundation"]
  windows:
    link: ["mylib", "ws2_32"]
```
