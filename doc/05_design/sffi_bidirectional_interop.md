# Design: SFFI Bidirectional Class Interop

**Related plan:** [phase4_sffi_implementation_plan.md](/doc/05_design/phase4_sffi_implementation_plan.md)
**Related architecture:** [doc/04_architecture/sffi_bidirectional_interop.md](../04_architecture/sffi_bidirectional_interop.md)

**Current repo state (2026-03-30):**
- Direction A export, manifest-backed Direction B extern registration, and the core verification suites are implemented.
- Runtime `spl_verify_layouts()` remains a follow-on extension; current safety relies on generated compile-time layout assertions and linting.

**Related requirements:**
- [doc/02_requirements/feature/usage/sffi_bidirectional_interop.md](../02_requirements/feature/usage/sffi_bidirectional_interop.md) (REQ-SFFI-BIDIR001–012)
- [doc/02_requirements/nfr/sffi_bidirectional_interop.md](../02_requirements/nfr/sffi_bidirectional_interop.md) (NFR-SFFI-001–004)

**Existing designs:**
- [doc/05_design/sffi_external_library_pattern.md](sffi_external_library_pattern.md) — 3-tier SFFI pattern
- [doc/05_design/cpp_wrapper_generator_design.md](cpp_wrapper_generator_design.md) — C++ wrapper gen
- [doc/05_design/phase4_sffi_implementation_plan.md](phase4_sffi_implementation_plan.md) — Phase 4 unblocking

---

## 1. Direction A: Simple -> C++ (Export)

### A1. @export("C") Attribute Parsing and Validation

**REQ:** REQ-SFFI-BIDIR001, REQ-SFFI-BIDIR012

#### A1.1 ExportAttr Struct

Add to `src/compiler/00.common/attributes.spl`:

```simple
struct ExportAttr:
    """Export attributes for C ABI interop."""
    is_export_c: bool       # @export("C") — export with C linkage
    export_name: text?      # @export("C", name: "custom_name") — custom symbol (nil = auto)

impl ExportAttr:
    static fn default() -> ExportAttr:
        ExportAttr(is_export_c: false, export_name: nil)

    fn has_export() -> bool:
        self.is_export_c
```

#### A1.2 parse_export_attrs() Function

Add to `src/compiler/00.common/attributes.spl`, following the pattern of `parse_function_attrs()`:

```simple
fn parse_export_attrs(attrs: [Attribute]) -> ExportAttr:
    """Extract export attributes from a list of attributes."""
    var is_export_c = false
    var export_name: text? = nil

    for attr in attrs:
        if attr.name == "export":
            if attr.args.len() > 0:
                val kind = extract_string_arg(attr.args[0])
                if kind == "C":
                    is_export_c = true
                    # Check for optional name argument: @export("C", name: "custom")
                    if attr.args.len() > 1:
                        val name = extract_string_arg(attr.args[1])
                        if name.len() > 0:
                            export_name = name

    ExportAttr(is_export_c: is_export_c, export_name: export_name)
```

This uses the existing `extract_string_arg()` helper already defined in `attributes.spl`.

#### A1.3 Validation Rules (Semantic Pass)

Add to `src/compiler/35.semantics/resolve.spl`:

```simple
fn validate_export_class(cls: HirClass) -> [Diagnostic]:
    """Validate that an @export("C") class meets C ABI requirements."""
    var diagnostics: [Diagnostic] = []

    if not cls.export_attr.is_export_c:
        return diagnostics

    # Rule 1: No generic type parameters
    if cls.type_params.len() > 0:
        diagnostics.push(Diagnostic.error(
            "SFFI001: @export(\"C\") class '{cls.name}' cannot have generic type parameters",
            cls.span
        ))

    # Rule 2: Must be public
    if not cls.is_public:
        diagnostics.push(Diagnostic.error(
            "@export(\"C\") class '{cls.name}' must be public",
            cls.span
        ))

    # Rule 3: All exported method parameters must be C-compatible
    for method_name, method_sym in cls.methods:
        val method = resolve_function(method_sym)
        for param in method.params:
            if not is_c_compatible_type(param.type_):
                diagnostics.push(Diagnostic.error(
                    "SFFI001: parameter '{param.name}' of method '{method_name}' has non-C-compatible type '{param.type_}'",
                    param.span
                ))

    # Rule 4: All fields must be C-compatible (for value-type exports)
    for field in cls.fields:
        if not is_c_compatible_type(field.type_):
            diagnostics.push(Diagnostic.error(
                "SFFI001: field '{field.name}' has non-C-compatible type '{field.type_}'",
                field.span
            ))

    diagnostics
```

C-compatible types: `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64`, `bool`, `text` (with warning), pointers to `@repr("C")` structs, opaque handles.

---

### A2. HirClass Changes

**REQ:** REQ-SFFI-BIDIR001

#### A2.1 New Fields on HirClass

Modify `src/compiler/20.hir/hir_definitions.spl`:

```simple
struct HirClass:
    """Class definition in HIR."""
    symbol: SymbolId
    name: text
    type_params: [HirTypeParam]
    fields: [HirField]
    methods: Dict<text, SymbolId>
    is_public: bool
    has_doc_comment: bool
    doc_comment: text
    span: Span
    has_layout_attr: bool
    layout_attr: LayoutAttr
    # --- NEW: Export attribute ---
    has_export_attr: bool
    export_attr: ExportAttr
    # --- END NEW ---
    is_generic_template: bool
    has_specialization_of: bool
    specialization_of: text
    type_bindings: Dict<text, HirType>
```

#### A2.2 HIR Lowering

Modify `src/compiler/20.hir/hir_lowering/items.spl` in the class lowering path:

```simple
# In lower_class():
val layout_attr = parse_layout_attrs(ast_class.attributes)
val export_attr = parse_export_attrs(ast_class.attributes)  # NEW

# ... construct HirClass with:
#   has_export_attr: export_attr.has_export(),
#   export_attr: export_attr,
```

---

### A3. MIR Changes

**REQ:** REQ-SFFI-BIDIR002

#### A3.1 MirFunction Export Metadata

Add export metadata to MIR functions in `src/compiler/50.mir/mir_data.spl`:

```simple
struct MirExportInfo:
    """Export metadata for C ABI."""
    is_exported: bool
    c_symbol_name: text       # e.g., "spl_Calculator_add"
    owning_class: text?       # e.g., "Calculator" (nil for standalone functions)
    is_constructor: bool
    is_destructor: bool
```

During MIR lowering, for each `@export("C")` class method, generate a wrapper `MirFunction` with:
- `export_info.is_exported = true`
- `export_info.c_symbol_name = "spl_{ClassName}_{methodName}"`
- The body delegates to the real Simple method

#### A3.2 Wrapper Function Generation Pattern

For a class method `Calculator.add(self, a: f64, b: f64) -> f64`, the MIR wrapper is conceptually:

```
fn spl_Calculator_add(handle: *void, a: f64, b: f64) -> f64:
    val self = cast<Calculator>(handle)
    return self.add(a, b)
```

For the constructor `Calculator.create(precision: i32) -> Calculator`:

```
fn spl_Calculator_create(precision: i32) -> *void:
    val obj = Calculator.create(precision)
    val handle = heap_alloc(obj)  # Pin on heap, return opaque pointer
    return cast<*void>(handle)
```

For the destructor:

```
fn spl_Calculator_destroy(handle: *void):
    val self = cast<Calculator>(handle)
    drop(self)                    # Run destructor + free
```

---

### A4. C Backend Changes

**REQ:** REQ-SFFI-BIDIR002

#### A4.1 emit_export_wrappers() on MirToC

Add to `src/compiler/70.backend/backend/c_backend_translate.spl`:

```simple
me emit_export_wrappers(module: MirModule):
    """Generate extern "C" wrapper functions for all @export("C") classes."""
    for _sym, func in module.functions:
        if func.export_info.? and func.export_info.unwrap().is_exported:
            val info = func.export_info.unwrap()
            self.emit_single_export_wrapper(func, info)

me emit_single_export_wrapper(func: MirFunction, info: MirExportInfo):
    """Emit a single extern "C" wrapper function."""
    val ret_type = self.type_mapper.map_type(func.return_type)
    var params_str = ""

    # Build parameter list
    for i, param in func.params.enumerate():
        if i > 0:
            params_str = params_str + ", "
        val c_type = self.type_mapper.map_type(param.type_)
        params_str = params_str + c_type + " " + param.name

    # Emit function
    self.builder.emit_raw("extern \"C\" {ret_type} {info.c_symbol_name}({params_str}) {{")
    # ... emit body that delegates to real function ...
    self.builder.emit_raw("}")
```

#### A4.2 Generated C++ Code Example

For `@export("C") class Calculator` with method `add(a: f64, b: f64) -> f64`:

```cpp
// --- Opaque handle typedef ---
typedef struct spl_Calculator* spl_Calculator_t;

// --- Constructor wrapper ---
extern "C" spl_Calculator_t spl_Calculator_create(int32_t precision) {
    // Allocate Calculator, call Simple constructor
    spl_Calculator* obj = (spl_Calculator*)spl_gc_alloc(sizeof(Calculator));
    Calculator_init(obj, precision);  // calls Simple's Calculator(precision: precision)
    return obj;
}

// --- Method wrapper ---
extern "C" double spl_Calculator_add(spl_Calculator_t self, double a, double b) {
    return Calculator_add((Calculator*)self, a, b);  // delegates to Simple method
}

// --- Destructor wrapper ---
extern "C" void spl_Calculator_destroy(spl_Calculator_t self) {
    Calculator_drop((Calculator*)self);  // calls Simple destructor
    spl_gc_free(self);
}

// --- Library lifecycle ---
extern "C" void spl_library_init(void) {
    __simple_runtime_init();
}

extern "C" void spl_library_shutdown(void) {
    __simple_runtime_shutdown();
}
```

#### A4.3 LLVM Backend Export

Modify `src/compiler/70.backend/backend/entry_point.spl` to emit exported functions with:

```llvm
define dso_local double @spl_Calculator_add(ptr %self, double %a, double %b) {
  ; delegate to @Calculator_add
  %result = call double @Calculator_add(ptr %self, double %a, double %b)
  ret double %result
}
```

Key LLVM attributes for exports:
- `dso_local` — symbol is defined in this DSO
- No `internal` or `private` linkage — must be externally visible
- `nounwind` — C functions should not unwind through C frames

---

### A5. Header Generation

**REQ:** REQ-SFFI-BIDIR003, REQ-SFFI-BIDIR004

#### A5.1 C Header Generator

New file: `src/compiler/90.tools/header_gen/c_header.spl`

Input: MIR module with export metadata
Output: `.h` file

**Generated structure:**

```c
/* Auto-generated by Simple compiler — DO NOT EDIT */
#ifndef SPL_CALCULATOR_H
#define SPL_CALCULATOR_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================ */
/* Library lifecycle                                             */
/* ============================================================ */
void spl_library_init(void);
void spl_library_shutdown(void);

/* ============================================================ */
/* Calculator — opaque handle                                    */
/* ============================================================ */
typedef struct spl_Calculator* spl_Calculator_t;

spl_Calculator_t spl_Calculator_create(int32_t precision);
void             spl_Calculator_destroy(spl_Calculator_t self);
double           spl_Calculator_add(spl_Calculator_t self, double a, double b);
double           spl_Calculator_multiply(spl_Calculator_t self, double a, double b);

#ifdef __cplusplus
}
#endif
#endif /* SPL_CALCULATOR_H */
```

#### A5.2 C++ Wrapper Header Generator

New file: `src/compiler/90.tools/header_gen/cpp_header.spl`

Input: Same MIR module
Output: `.hpp` file

**Generated structure:**

```cpp
// Auto-generated by Simple compiler — DO NOT EDIT
#pragma once
#include "calculator.h"
#include <utility>  // std::move

namespace spl {

class Calculator {
    spl_Calculator_t handle_;

public:
    /// Construct a Calculator with given precision.
    explicit Calculator(int32_t precision)
        : handle_(spl_Calculator_create(precision)) {}

    /// Destructor — releases underlying Simple object.
    ~Calculator() {
        if (handle_) spl_Calculator_destroy(handle_);
    }

    // Non-copyable
    Calculator(const Calculator&) = delete;
    Calculator& operator=(const Calculator&) = delete;

    // Movable
    Calculator(Calculator&& other) noexcept
        : handle_(other.handle_) { other.handle_ = nullptr; }
    Calculator& operator=(Calculator&& other) noexcept {
        if (this != &other) {
            if (handle_) spl_Calculator_destroy(handle_);
            handle_ = other.handle_;
            other.handle_ = nullptr;
        }
        return *this;
    }

    /// Add two numbers.
    double add(double a, double b) {
        return spl_Calculator_add(handle_, a, b);
    }

    /// Multiply two numbers.
    double multiply(double a, double b) {
        return spl_Calculator_multiply(handle_, a, b);
    }

    /// Access the raw handle (for interop).
    spl_Calculator_t raw_handle() const { return handle_; }
};

} // namespace spl
```

#### A5.3 Type Mapping (CTypeMapper Reuse)

The header generator reuses `CTypeMapper` from `src/compiler/70.backend/backend/common/type_mapper.spl`:

| Simple Type | C Type | C++ Type |
|-------------|--------|----------|
| `i8` | `int8_t` | `int8_t` |
| `i16` | `int16_t` | `int16_t` |
| `i32` | `int32_t` | `int32_t` |
| `i64` | `int64_t` | `int64_t` |
| `u8` | `uint8_t` | `uint8_t` |
| `u16` | `uint16_t` | `uint16_t` |
| `u32` | `uint32_t` | `uint32_t` |
| `u64` | `uint64_t` | `uint64_t` |
| `f32` | `float` | `float` |
| `f64` | `double` | `double` |
| `bool` | `bool` (with `<stdbool.h>`) | `bool` |
| `text` | `const char*` (UTF-8) | `std::string_view` or `const char*` |
| `@export("C") class Foo` | `spl_Foo_t` (opaque handle) | `spl::Foo` (wrapper class) |
| `[T]` (array) | `spl_array_t` (opaque) | `spl::Array<T>` |
| `Option<T>` | `T` + bool flag, or nullable pointer | `std::optional<T>` |

---

### A6. Shared Library Build

**REQ:** REQ-SFFI-BIDIR008, REQ-SFFI-BIDIR009

#### A6.1 Linker Mode: link_to_shared()

Add to `src/compiler/70.backend/linker/linker_wrapper.spl`:

```simple
fn link_to_shared(config: LinkerConfig, object_files: [text], output: text) -> Result<text, text>:
    """Link object files into a shared library."""
    var args: [text] = []

    if config.target.is_linux():
        args.push("-shared")
        args.push("-fPIC")
        args.push("-Wl,--version-script={config.export_map}")
        val so_name = output + ".so"
        args.push("-o")
        args.push(so_name)
    elif config.target.is_macos():
        args.push("-dynamiclib")
        args.push("-Wl,-exported_symbols_list,{config.export_list}")
        val dylib_name = output + ".dylib"
        args.push("-o")
        args.push(dylib_name)
    elif config.target.is_windows():
        # MSVC: cl /LD or link /DLL
        args.push("/DLL")
        args.push("/DEF:{config.export_def}")
        args.push("/OUT:{output}.dll")
        args.push("/IMPLIB:{output}.lib")

    for obj in object_files:
        args.push(obj)

    # Link against Simple runtime
    args.push("-lsimple_runtime")

    invoke_linker(config.linker, args)
```

#### A6.2 Export Map Generation

For Linux, generate a version script (`.map`):

```
SPL_1.0 {
    global:
        spl_library_init;
        spl_library_shutdown;
        spl_Calculator_create;
        spl_Calculator_destroy;
        spl_Calculator_add;
        spl_Calculator_multiply;
    local:
        *;
};
```

For macOS, generate an exported symbols list:

```
_spl_library_init
_spl_library_shutdown
_spl_Calculator_create
_spl_Calculator_destroy
_spl_Calculator_add
_spl_Calculator_multiply
```

For Windows, generate a `.def` file:

```
LIBRARY mylib
EXPORTS
    spl_library_init
    spl_library_shutdown
    spl_Calculator_create
    spl_Calculator_destroy
    spl_Calculator_add
    spl_Calculator_multiply
```

#### A6.3 Runtime Library Init

Add to `src/runtime/runtime.h` and `src/runtime/runtime.c`:

```c
/* Thread-safe library initialization */
static _Atomic int spl_init_count = 0;

void spl_library_init(void) {
    if (atomic_fetch_add(&spl_init_count, 1) == 0) {
        __simple_runtime_init();
    }
}

void spl_library_shutdown(void) {
    if (atomic_fetch_sub(&spl_init_count, 1) == 1) {
        __simple_runtime_shutdown();
    }
}
```

Auto-init (opt-in via `--auto-init`):

```c
/* Linux/macOS: auto-init on library load */
__attribute__((constructor))
static void spl_auto_init(void) { spl_library_init(); }

__attribute__((destructor))
static void spl_auto_shutdown(void) { spl_library_shutdown(); }
```

```c
/* Windows: auto-init via DllMain */
BOOL WINAPI DllMain(HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpvReserved) {
    if (fdwReason == DLL_PROCESS_ATTACH) spl_library_init();
    if (fdwReason == DLL_PROCESS_DETACH) spl_library_shutdown();
    return TRUE;
}
```

#### A6.4 Driver CLI Integration

Modify `src/compiler/80.driver/driver_api.spl`:

```simple
# New build modes
# --shared          Produce shared library (.so/.dylib/.dll)
# --emit-header     Generate C header (.h)
# --emit-cxx-header Generate C++ wrapper header (.hpp)
# --auto-init       Enable auto-initialization on library load
```

**Usage:**

```bash
# Full shared library build with headers
bin/simple build --shared --emit-header --emit-cxx-header \
    --entry src/mylib.spl -o build/libmylib

# Output:
#   build/libmylib.so          (or .dylib / .dll)
#   build/libmylib.h           (C header)
#   build/libmylib.hpp         (C++ wrapper header)
```

---

## 2. Direction C: Layout Verification

### C1. @repr("C") — Already Exists

**REQ:** REQ-SFFI-BIDIR005

The `@repr("C")` attribute is already fully implemented:

- **LayoutKind.C enum variant**: `src/compiler/30.types/type_layout.spl:45-50`
- **parse_layout_attrs()**: `src/compiler/00.common/attributes.spl` — parses `@repr("C")` -> `LayoutKind.C`
- **HirClass.layout_attr**: `src/compiler/20.hir/hir_definitions.spl` — stores `LayoutAttr` on classes
- **compute_c_abi_layout()**: `src/compiler/30.types/type_layout.spl` — computes C-compatible field offsets

What needs adding: **enforcement** that `@export("C")` classes either:
1. Use opaque handle pattern (default, no layout concern), OR
2. Have `@repr("C")` if any struct is passed by value across the FFI boundary

### C2. Layout Computation for _Static_assert

**REQ:** REQ-SFFI-BIDIR006

#### C2.1 Extend type_layout.spl

The existing `compute_c_abi_layout()` in `src/compiler/30.types/type_layout.spl` already computes field offsets with C alignment rules. Extend it to export verification data:

```simple
struct LayoutVerification:
    """Layout data for _Static_assert generation."""
    class_name: text
    total_size: i64
    alignment: i64
    field_offsets: [(text, i64)]   # (field_name, byte_offset) pairs

fn compute_layout_verification(cls: HirClass, arch: Architecture) -> LayoutVerification:
    """Compute layout verification data for an @repr("C") class."""
    val field_types = cls.fields.map(\f: (f.name, f.type_))
    val layout = compute_struct_layout_for_arch(field_types, cls.layout_attr, arch)

    var offsets: [(text, i64)] = []
    for i, field in cls.fields.enumerate():
        offsets.push((field.name, layout.field_layouts[i].offset))

    LayoutVerification(
        class_name: cls.name,
        total_size: layout.size,
        alignment: layout.alignment,
        field_offsets: offsets
    )
```

#### C2.2 _Static_assert Emission in C Header

The layout verifier in `src/compiler/90.tools/header_gen/layout_verifier.spl` emits:

```c
/* Layout verification for PacketHeader — auto-generated */
struct spl_PacketHeader {
    uint8_t  version;
    uint8_t  flags;
    uint16_t length;
    uint32_t sequence;
};

_Static_assert(sizeof(struct spl_PacketHeader) == 8, "spl_PacketHeader size mismatch");
_Static_assert(_Alignof(struct spl_PacketHeader) == 4, "spl_PacketHeader alignment mismatch");
_Static_assert(offsetof(struct spl_PacketHeader, version)  == 0, "version offset mismatch");
_Static_assert(offsetof(struct spl_PacketHeader, flags)    == 1, "flags offset mismatch");
_Static_assert(offsetof(struct spl_PacketHeader, length)   == 2, "length offset mismatch");
_Static_assert(offsetof(struct spl_PacketHeader, sequence) == 4, "sequence offset mismatch");
```

If the C compiler's layout differs from Simple's computed layout, compilation fails with a clear message — catching ABI bugs at compile time, not at runtime.

### C3. SFFI Lint Rules

**REQ:** REQ-SFFI-BIDIR007

New file: `src/compiler/35.semantics/lint/sffi_lint.spl`

Following the pattern from `src/compiler/35.semantics/lint/remote_exec_lint.spl`:

```simple
# SFFI Lint Rules
#
# Compile-time checks for FFI type safety.
#
# SFFI001: Non-C-compatible type in @export("C") class       ERROR
# SFFI002: text field in @export("C") class                  WARNING
# SFFI003: Struct by-value across FFI without @repr("C")     ERROR
# SFFI004: Bitfield without @bits(N) in FFI struct            ERROR
# SFFI005: Platform-dependent type in FFI struct              WARNING

# ============================================================================
# Warning Struct
# ============================================================================

struct SffiWarning:
    """A single SFFI lint warning."""
    rule: text          # "SFFI001", "SFFI002", etc.
    severity: text      # "error" or "warning"
    message: text
    file: text
    line: i64
    column: i64

# ============================================================================
# SFFI001: Non-C-Compatible Type
# ============================================================================

fn check_sffi001(cls: HirClass) -> [SffiWarning]:
    """Check for non-C-compatible field types in @export("C") classes."""
    var warnings: [SffiWarning] = []

    if not cls.export_attr.is_export_c:
        return warnings

    val non_c_types = ["Closure", "Fn", "dyn", "impl"]

    for field in cls.fields:
        val type_name = field.type_.to_text()
        for bad in non_c_types:
            if type_name.contains(bad):
                warnings.push(SffiWarning(
                    rule: "SFFI001",
                    severity: "error",
                    message: "field '{field.name}' has non-C-compatible type '{type_name}' in @export(\"C\") class '{cls.name}'. Closures, generics, and trait objects cannot cross the FFI boundary.",
                    file: cls.span.file,
                    line: field.span.line,
                    column: field.span.column
                ))

    # Also check generic type params on the class itself
    if cls.type_params.len() > 0:
        warnings.push(SffiWarning(
            rule: "SFFI001",
            severity: "error",
            message: "@export(\"C\") class '{cls.name}' has generic type parameters. Generic classes cannot be exported to C.",
            file: cls.span.file,
            line: cls.span.line,
            column: cls.span.column
        ))

    warnings

# ============================================================================
# SFFI002: text Field Warning
# ============================================================================

fn check_sffi002(cls: HirClass) -> [SffiWarning]:
    """Warn about text fields in @export("C") classes."""
    var warnings: [SffiWarning] = []

    if not cls.export_attr.is_export_c:
        return warnings

    for field in cls.fields:
        if field.type_.to_text() == "text":
            warnings.push(SffiWarning(
                rule: "SFFI002",
                severity: "warning",
                message: "field '{field.name}' has type 'text' in @export(\"C\") class '{cls.name}'. Text requires special marshalling across FFI — consider using 'const char*' via extern fn or explicit conversion.",
                file: cls.span.file,
                line: field.span.line,
                column: field.span.column
            ))

    warnings

# ============================================================================
# SFFI003: Struct By-Value Without @repr("C")
# ============================================================================

fn check_sffi003_param(param_type: HirType, param_name: text, fn_name: text, span: Span) -> [SffiWarning]:
    """Check if a by-value struct parameter in an FFI function has @repr("C")."""
    var warnings: [SffiWarning] = []

    # Only applies to struct/class types (not primitives, not pointers)
    if param_type.is_struct_or_class() and not param_type.is_pointer():
        val resolved_class = resolve_type_class(param_type)
        if resolved_class.? and not resolved_class.unwrap().layout_attr.layout_kind == LayoutKind.C:
            warnings.push(SffiWarning(
                rule: "SFFI003",
                severity: "error",
                message: "struct '{param_type.to_text()}' passed by value in FFI function '{fn_name}' (parameter '{param_name}') without @repr(\"C\"). Add @repr(\"C\") to the struct definition to guarantee C-compatible layout.",
                file: span.file,
                line: span.line,
                column: span.column
            ))

    warnings

# ============================================================================
# SFFI004: Bitfield Without @bits(N)
# ============================================================================

fn check_sffi004(cls: HirClass) -> [SffiWarning]:
    """Check for bitfields without @bits(N) in FFI structs."""
    var warnings: [SffiWarning] = []

    if not cls.export_attr.is_export_c:
        return warnings
    if cls.layout_attr.layout_kind != LayoutKind.C:
        return warnings

    for field in cls.fields:
        # If the field name suggests a bitfield or the type is smaller than
        # the storage type, require @bits(N)
        if field.has_bits_attr and not field.has_explicit_bits_width:
            warnings.push(SffiWarning(
                rule: "SFFI004",
                severity: "error",
                message: "bitfield '{field.name}' in @repr(\"C\") @export(\"C\") class '{cls.name}' lacks explicit @bits(N) width. C bitfield packing is implementation-defined — explicit widths ensure cross-platform consistency.",
                file: cls.span.file,
                line: field.span.line,
                column: field.span.column
            ))

    warnings

# ============================================================================
# SFFI005: Platform-Dependent Type Size
# ============================================================================

fn check_sffi005(cls: HirClass) -> [SffiWarning]:
    """Warn about platform-dependent type sizes in FFI structs."""
    var warnings: [SffiWarning] = []

    if not cls.export_attr.is_export_c:
        return warnings

    val platform_dependent = ["isize", "usize"]

    for field in cls.fields:
        val type_name = field.type_.to_text()
        for pd_type in platform_dependent:
            if type_name == pd_type:
                warnings.push(SffiWarning(
                    rule: "SFFI005",
                    severity: "warning",
                    message: "field '{field.name}' has platform-dependent type '{type_name}' in @export(\"C\") class '{cls.name}'. Use fixed-width types (i32, i64, etc.) for portable FFI.",
                    file: cls.span.file,
                    line: field.span.line,
                    column: field.span.column
                ))

    warnings

# ============================================================================
# Run All SFFI Checks
# ============================================================================

fn run_sffi_lint(cls: HirClass) -> [SffiWarning]:
    """Run all SFFI lint rules on a class."""
    var all_warnings: [SffiWarning] = []
    all_warnings.extend(check_sffi001(cls))
    all_warnings.extend(check_sffi002(cls))
    all_warnings.extend(check_sffi004(cls))
    all_warnings.extend(check_sffi005(cls))
    all_warnings

fn run_sffi_lint_function(func: HirFunction) -> [SffiWarning]:
    """Run SFFI lint on a function's parameters (SFFI003 check)."""
    var all_warnings: [SffiWarning] = []

    # Check if this function is in an @export("C") context or is extern
    if func.is_extern or func.export_attr.is_export_c:
        for param in func.params:
            all_warnings.extend(check_sffi003_param(
                param.type_, param.name, func.name, param.span
            ))

    all_warnings
```

#### C3.1 Lint Rule Summary with Examples

**SFFI001 — Non-C-compatible type (ERROR):**

```simple
# BAD: triggers SFFI001
@export("C")
class BadExport:
    callback: Fn<(i32) -> i32>    # ERROR: closure type
    items: List<i32>              # ERROR: generic type

# GOOD: only C-compatible types
@export("C")
class GoodExport:
    count: i32
    value: f64
```

**SFFI002 — text field (WARNING):**

```simple
# WARN: text requires marshalling
@export("C")
class NamedThing:
    name: text    # WARNING: consider const char* via extern fn
    id: i32       # OK
```

**SFFI003 — Struct by-value without @repr("C") (ERROR):**

```simple
# BAD: Point lacks @repr("C")
class Point:
    x: f64
    y: f64

@export("C")
fn distance(p: Point) -> f64:   # ERROR: Point by-value without @repr("C")
    pass_todo

# GOOD: add @repr("C")
@repr("C")
class Point:
    x: f64
    y: f64
```

**SFFI004 — Bitfield without @bits(N) (ERROR):**

```simple
# BAD: no explicit width
@repr("C")
@export("C")
class BadRegister:
    mode: u8        # ERROR if intended as bitfield without @bits

# GOOD: explicit widths
@repr("C")
@export("C")
class GoodRegister:
    @bits(4) mode: u8
    @bits(1) output: u8
    @bits(1) input: u8
    @bits(2) speed: u8
```

**SFFI005 — Platform-dependent type (WARNING):**

```simple
# WARN: usize varies by platform
@export("C")
class Buffer:
    size: usize     # WARNING: use u64 or u32 for portable FFI
    data: u8
```

---

## 3. C5. Bitfield Support

**REQ:** REQ-SFFI-BIDIR010

### C5.1 @bits(N) Attribute

```simple
@repr("C")
@export("C")
class GpioRegister:
    @bits(4) mode: u8       # 4-bit field
    @bits(1) output: u8     # 1-bit field
    @bits(1) input: u8      # 1-bit field
    @bits(2) speed: u8      # 2-bit field
```

### C5.2 Generated C Struct

```c
struct spl_GpioRegister {
    uint8_t mode   : 4;
    uint8_t output : 1;
    uint8_t input  : 1;
    uint8_t speed  : 2;
};

_Static_assert(sizeof(struct spl_GpioRegister) == 1, "GpioRegister size mismatch");
```

### C5.3 Bitfield Packing Rules

Simple follows the C bitfield packing rules for the target platform:
- Fields pack into the underlying storage unit (`u8`, `u16`, `u32`, `u64`)
- A field that would cross a storage unit boundary starts a new unit
- `@bits(0)` forces alignment to next storage unit boundary
- The compiler computes exact byte sizes and verifies via `_Static_assert`

---

## 4. Runtime Layout Verification (Deferred)

**REQ:** REQ-SFFI-BIDIR006

This section describes a possible follow-on extension. The current implementation does not emit `spl_verify_layouts()` and instead relies on generated `_Static_assert` / `static_assert` checks in the emitted headers.

If runtime layout verification is added later, the library init path can call `spl_verify_layouts()`:

```c
void spl_verify_layouts(void) {
    /* Auto-generated by Simple compiler */
    assert(sizeof(struct spl_PacketHeader) == 8
        && "PacketHeader size mismatch — recompile headers");
    assert(offsetof(struct spl_PacketHeader, version) == 0
        && "PacketHeader.version offset mismatch");
    assert(offsetof(struct spl_PacketHeader, flags) == 1
        && "PacketHeader.flags offset mismatch");
    assert(offsetof(struct spl_PacketHeader, length) == 2
        && "PacketHeader.length offset mismatch");
    assert(offsetof(struct spl_PacketHeader, sequence) == 4
        && "PacketHeader.sequence offset mismatch");
}
```

This catches cross-compiler ABI differences that `_Static_assert` alone cannot detect (e.g., when the header was compiled with GCC but the library with Clang, and they disagree on bitfield packing).

---

## 5. Files Modified and Created

### Modified Files

| File | Change | REQ |
|------|--------|-----|
| `src/compiler/00.common/attributes.spl` | Add `ExportAttr`, `parse_export_attrs()` | BIDIR001 |
| `src/compiler/20.hir/hir_definitions.spl` | Add `has_export_attr`, `export_attr` to `HirClass` | BIDIR001 |
| `src/compiler/20.hir/hir_lowering/items.spl` | Call `parse_export_attrs()` during class lowering | BIDIR001 |
| `src/compiler/35.semantics/resolve.spl` | Add `validate_export_class()` | BIDIR001 |
| `src/compiler/50.mir/mir_data.spl` | Add `MirExportInfo` to `MirFunction` | BIDIR002 |
| `src/compiler/70.backend/backend/c_backend_translate.spl` | Add `emit_export_wrappers()`, `emit_library_init()` | BIDIR002 |
| `src/compiler/70.backend/backend/entry_point.spl` | Add `dso_local` export for LLVM backend | BIDIR002 |
| `src/compiler/70.backend/linker/linker_wrapper.spl` | Add `link_to_shared()` | BIDIR008 |
| `src/compiler/80.driver/driver_api.spl` | Add `--shared`, `--emit-header`, `--emit-cxx-header` flags | BIDIR008 |
| `src/compiler/30.types/type_layout.spl` | Add `compute_layout_verification()`, `LayoutVerification` | BIDIR006 |
| `src/compiler/70.backend/backend/c_backend_translate.spl` | Emit guarded `spl_library_init()` / `spl_library_shutdown()` definitions and auto-init hooks | BIDIR009 |
| `src/compiler/90.tools/header_gen/c_header.spl` | Emit lifecycle declarations in generated headers | BIDIR009 |

### New Files

| File | Purpose | REQ |
|------|---------|-----|
| `src/compiler/35.semantics/lint/sffi_lint.spl` | SFFI001-005 lint rules | BIDIR007 |
| `src/compiler/90.tools/header_gen/mod.spl` | Header generation entry point | BIDIR003 |
| `src/compiler/90.tools/header_gen/c_header.spl` | C `.h` emitter | BIDIR003 |
| `src/compiler/90.tools/header_gen/cpp_header.spl` | C++ `.hpp` wrapper emitter | BIDIR004 |
| `src/compiler/90.tools/header_gen/layout_verifier.spl` | Layout verification + `_Static_assert` gen | BIDIR006 |

---

## 6. Traceability Matrix

| Requirement | Design Section | Implementation File |
|-------------|---------------|---------------------|
| REQ-SFFI-BIDIR001 | A1, A2 | attributes.spl, hir_definitions.spl |
| REQ-SFFI-BIDIR002 | A3, A4 | mir_data.spl, c_backend_translate.spl |
| REQ-SFFI-BIDIR003 | A5.1 | header_gen/c_header.spl |
| REQ-SFFI-BIDIR004 | A5.2 | header_gen/cpp_header.spl |
| REQ-SFFI-BIDIR005 | C1 | type_layout.spl (existing) |
| REQ-SFFI-BIDIR006 | C2 | type_layout.spl, header_gen/layout_verifier.spl |
| REQ-SFFI-BIDIR007 | C3 | lint/sffi_lint.spl |
| REQ-SFFI-BIDIR008 | A6.1 | linker_wrapper.spl |
| REQ-SFFI-BIDIR009 | A6.3 | c_backend_translate.spl, c_header.spl |
| REQ-SFFI-BIDIR010 | C5 | type_layout.spl, c_header.spl |
| REQ-SFFI-BIDIR011 | B1 | interpreter_eval.rs, dynamic_ffi.rs, plugin_manifest.rs, src/app/plugin/ |
| REQ-SFFI-BIDIR012 | A1, A4 | attributes.spl, c_backend_translate.spl |
| NFR-SFFI-001 | A6.1 | linker_wrapper.spl (3-platform) |
| NFR-SFFI-002 | C1, C2 | type_layout.spl, layout_verifier.spl |
| NFR-SFFI-003 | A4 | c_backend_translate.spl (thin wrappers) |
| NFR-SFFI-004 | C3 | lint/sffi_lint.spl |
