# SFFI Bidirectional Class Interop

**Feature:** SFFI Bidirectional Class Interop
**Status:** Implemented
**Created:** 2026-03-28
**Plan:** [phase4_sffi_implementation_plan.md](/doc/05_design/phase4_sffi_implementation_plan.md)
**Related design:** [sffi_external_library_pattern.md](/doc/05_design/sffi_external_library_pattern.md), [cpp_wrapper_generator_design.md](/doc/05_design/cpp_wrapper_generator_design.md), [phase4_sffi_implementation_plan.md](/doc/05_design/phase4_sffi_implementation_plan.md)
**Related research:** [sffi_dynamic_loading_2026-02-21.md](/doc/01_research/local/sffi_dynamic_loading_2026-02-21.md)
**NFR:** [sffi_bidirectional_interop.md](/doc/02_requirements/nfr/sffi_bidirectional_interop.md)

## Overview

Simple's SFFI currently supports calling C/C++ functions from Simple (`extern fn rt_*`), but not the reverse direction. This feature adds **bidirectional class-level interop** so that:

- **Direction A (Simple -> C/C++):** A Simple class annotated with `@export("C")` can be compiled into a shared library and used from C or C++ code, with auto-generated headers.
- **Direction B (C++ -> Simple):** A plugin manifest system unblocks the existing three-tier SFFI pattern so C++ classes can be wrapped and used from Simple without semantic analyzer rejection.
- **Layout Safety:** Compile-time struct layout verification, lint rules, and bitfield support prevent silent data corruption across the FFI boundary.

This is critical for incremental migration of C++ codebases to Simple, where both directions must coexist.

### Current State

| Direction | Status | Mechanism |
|-----------|--------|-----------|
| Simple -> C/C++ export | IMPLEMENTED | `@export("C")` wrappers + generated `.h` / `.hpp` headers + shared-library build mode |
| C/C++ -> Simple wrapper registration | IMPLEMENTED | `.wrapper_spec` -> manifest scaffold -> `extern fn` acceptance via plugin manifest + runtime dynamic loading |
| Runtime layout verification helper | DEFERRED | Compile-time layout checks implemented; runtime `spl_verify_layouts()` remains a future extension |

### Existing Infrastructure

- `extern class` syntax (parsed, tested)
- `.wrapper_spec` parser (`src/app/wrapper_gen/spec_parser.spl`)
- `CTypeMapper` (`src/compiler/70.backend/backend/common/type_mapper.spl`)
- `@callconv("C")` (`src/compiler/70.backend/callconv_bridge.spl`)
- C backend (`src/compiler/70.backend/backend/c_backend_translate.spl`)

---

## Requirements

### REQ-SFFI-BIDIR001: @export("C") Attribute on Classes

**Priority:** P0
**Dependencies:** None

**Description:**
The `@export("C")` attribute, when applied to a class definition, marks that class for C ABI export. The compiler shall validate that the class contains only C-compatible field types (no generics initially), is a top-level class, and collects the exported class along with its method signatures for downstream code generation.

**Rationale:**
This is the entry point for Direction A (Simple -> C/C++). Without a way to mark classes for export, no C ABI functions or headers can be generated. The attribute-based approach is consistent with Simple's existing decorator patterns and keeps the export decision explicit.

**Acceptance Criteria:**
1. `@export("C")` can be applied to any top-level class definition without compilation errors.
2. The compiler rejects `@export("C")` on classes with non-C-compatible field types (e.g., `text` without special handling, generic type parameters, closures) with a clear diagnostic message.
3. The compiler rejects `@export("C")` on nested or anonymous classes.
4. The semantic analyzer collects all `@export("C")` classes and their method signatures into a registry accessible by later compilation phases.
5. Classes without `@export("C")` are not affected in any way.

---

### REQ-SFFI-BIDIR002: C ABI Function Generation

**Priority:** P0
**Dependencies:** REQ-SFFI-BIDIR001

**Description:**
For each class annotated with `@export("C")`, the compiler shall automatically generate `extern "C"` functions that expose the class constructor, destructor, and all public methods through a C-compatible ABI. The generated functions use an opaque handle pattern where the Simple object is stored behind a pointer and accessed via a handle type.

**Rationale:**
C does not have classes or methods. To make Simple classes callable from C, each method must be exposed as a standalone function with a handle parameter. This opaque handle pattern is the industry-standard approach (used by SQLite, OpenSSL, GTK, etc.) and preserves encapsulation.

**Acceptance Criteria:**
1. For a class `Foo` with a static factory `create(...)`, the compiler generates `spl_Foo_create(...)` returning an opaque handle `spl_Foo_t`.
2. For each public method `bar(self, x: i32) -> f64`, the compiler generates `spl_Foo_bar(spl_Foo_t self, int32_t x) -> double`.
3. A destructor function `spl_Foo_destroy(spl_Foo_t self)` is generated that properly frees the underlying Simple object.
4. The naming convention follows `spl_{ClassName}_{methodName}` consistently.
5. All generated functions have `extern "C"` linkage (C backend) or `dso_local` external linkage (LLVM backend).
6. Mutable methods (declared with `me`) are handled correctly through the handle.
7. Parameter and return types are mapped through `CTypeMapper`.

---

### REQ-SFFI-BIDIR003: C Header Generation

**Priority:** P1
**Dependencies:** REQ-SFFI-BIDIR001, REQ-SFFI-BIDIR002

**Description:**
The compiler shall emit a C header file (`.h`) for all `@export("C")` classes and functions, containing opaque handle typedefs, function declarations, and include guards. The header is generated via a new `--emit-header` CLI flag.

**Rationale:**
C/C++ consumers need a header file to call the exported functions. Auto-generating it from the source of truth (the Simple class definition) eliminates manual synchronization errors and ensures the header always matches the compiled library.

**Acceptance Criteria:**
1. Running `bin/simple build --emit-header` produces a `.h` file for each module containing `@export("C")` items.
2. The header includes `#ifndef` / `#define` / `#endif` include guards.
3. The header wraps declarations in `#ifdef __cplusplus extern "C" { ... }` for C++ compatibility.
4. Each exported class produces an opaque handle typedef: `typedef struct spl_ClassName* spl_ClassName_t;`.
5. All generated C ABI functions (REQ-SFFI-BIDIR002) have corresponding declarations in the header.
6. Type mappings use standard C types (`int32_t`, `double`, `uint8_t`, etc.) from `<stdint.h>`.
7. The header includes `spl_library_init()` and `spl_library_shutdown()` declarations.
8. The generated header compiles cleanly with `gcc -Wall -Wextra -pedantic` and `clang -Wall`.

---

### REQ-SFFI-BIDIR004: C++ Wrapper Generation

**Priority:** P1
**Dependencies:** REQ-SFFI-BIDIR003

**Description:**
The compiler shall emit a C++ wrapper header (`.hpp`) that provides RAII wrapper classes delegating to the C ABI functions. The wrapper classes support move semantics, prevent copying, and provide method-call syntax matching the original Simple class interface. Generated via `--emit-cxx-header` CLI flag.

**Rationale:**
C++ developers expect RAII resource management and method-call syntax. A generated `.hpp` wrapper makes Simple classes feel native in C++ codebases, enabling drop-in replacement during incremental migration from C++ to Simple.

**Acceptance Criteria:**
1. Running `bin/simple build --emit-cxx-header` produces a `.hpp` file for each module containing `@export("C")` items.
2. Each exported class generates a C++ wrapper class in the `spl` namespace.
3. The wrapper class constructor calls the corresponding `spl_ClassName_create(...)` function.
4. The wrapper class destructor calls `spl_ClassName_destroy(handle_)`.
5. The wrapper class is non-copyable (`= delete` on copy constructor and copy assignment).
6. The wrapper class is movable (move constructor transfers handle ownership, sets source to `nullptr`).
7. Each public method delegates to the corresponding `spl_ClassName_methodName(handle_, ...)` function.
8. The wrapper includes `#include "classname.h"` to reference the C header.
9. The generated header compiles cleanly with `clang++ -std=c++17 -Wall`.

---

### REQ-SFFI-BIDIR005: @repr("C") Attribute

**Priority:** P0
**Dependencies:** None

**Description:**
The `@repr("C")` attribute, when applied to a class or struct, forces C-compatible struct layout: no field reordering, C alignment rules, and explicit padding. This attribute is required on any struct passed by value across the FFI boundary.

**Rationale:**
Simple may reorder fields for memory optimization, which would silently corrupt data when a struct is shared with C/C++ code. `@repr("C")` guarantees deterministic layout matching C's struct layout rules, preventing a class of subtle and dangerous FFI bugs.

**Acceptance Criteria:**
1. `@repr("C")` can be applied to any class or struct definition.
2. Fields in an `@repr("C")` struct are laid out in declaration order with no reordering.
3. Alignment and padding follow C ABI rules for the target platform.
4. The compiler computes and stores field offsets, total struct size, and padding bytes for each `@repr("C")` type.
5. Passing a struct by value across an FFI boundary without `@repr("C")` triggers lint rule SFFI003 (see REQ-SFFI-BIDIR007).
6. `@repr("C")` structs can be used independently of `@export("C")` (for C -> Simple direction too).

---

### REQ-SFFI-BIDIR006: Compile-Time Layout Verification

**Priority:** P0
**Dependencies:** REQ-SFFI-BIDIR005

**Description:**
For every `@repr("C")` struct included in a generated C header, the compiler shall emit `_Static_assert` statements verifying `sizeof` and `offsetof` for each field. These assertions are compiled by the C/C++ compiler, catching any layout mismatch between the Simple compiler's computation and the target C compiler's layout.

**Rationale:**
Different compilers (MSVC, GCC, Clang) may compute different struct layouts depending on alignment settings, packing pragmas, and platform ABI. Compile-time assertions provide a zero-cost safety net that catches mismatches before any code runs, preventing silent data corruption.

**Acceptance Criteria:**
1. Every `@repr("C")` struct in a generated `.h` header includes `_Static_assert(sizeof(spl_StructName) == N, "size mismatch")`.
2. Every field in the struct includes `_Static_assert(offsetof(spl_StructName, field) == N, "offset mismatch")`.
3. The asserted values match the Simple compiler's computed layout for the target platform.
4. If a C compiler rejects a `_Static_assert`, the error message clearly identifies which struct and field has a mismatch.
5. The assertions use `_Static_assert` (C11) or `static_assert` (C++11) depending on the header type.
6. Layout computation supports at minimum: `i8`/`u8`, `i16`/`u16`, `i32`/`u32`, `i64`/`u64`, `f32`/`f64`, pointer types.

---

### REQ-SFFI-BIDIR007: SFFI Lint Rules (SFFI001-SFFI005)

**Priority:** P0
**Dependencies:** REQ-SFFI-BIDIR001, REQ-SFFI-BIDIR005

**Description:**
The compiler shall include five SFFI-specific lint rules that detect unsafe or incorrect FFI type usage at compile time:

| Rule | Severity | Trigger |
|------|----------|---------|
| SFFI001 | ERROR | `@export("C")` class has a non-C-compatible field type (closures, generics, trait objects) |
| SFFI002 | WARNING | `@export("C")` class has a `text` field (pointer type, requires special marshalling) |
| SFFI003 | ERROR | Struct passed by value across FFI boundary without `@repr("C")` |
| SFFI004 | ERROR | Bitfield used in FFI struct without explicit `@bits(N)` width annotation |
| SFFI005 | WARNING | Platform-dependent type size in FFI struct (e.g., `int` varies by platform) |

**Rationale:**
FFI bugs are among the hardest to debug because they manifest as silent data corruption, segfaults, or undefined behavior. Catching these at compile time with clear diagnostics prevents hours of debugging and eliminates entire classes of FFI errors. This is especially important during C++ -> Simple migration where FFI boundaries are temporary and numerous.

**Acceptance Criteria:**
1. SFFI001 emits an error when `@export("C")` is applied to a class with closure, generic, or trait object fields, with a message naming the offending field and type.
2. SFFI002 emits a warning when `@export("C")` is applied to a class with `text` fields, suggesting explicit string handling.
3. SFFI003 emits an error when a struct without `@repr("C")` appears as a by-value parameter or return type in an `extern fn` or `@export("C")` method signature.
4. SFFI004 emits an error when a field in an `@repr("C")` struct uses a bitfield without an explicit `@bits(N)` annotation.
5. SFFI005 emits a warning when an FFI struct field uses a platform-dependent type.
6. All lint rules are active by default and can be individually suppressed with `@allow(SFFI00N)`.
7. Running `bin/simple build lint` on a file with SFFI issues reports all applicable rules.

---

### REQ-SFFI-BIDIR008: Shared Library Build Mode

**Priority:** P1
**Dependencies:** REQ-SFFI-BIDIR002

**Description:**
The build system shall support a `--shared` flag that produces a shared library (`.so` on Linux, `.dylib` on macOS, `.dll` on Windows) instead of an executable. The shared library exports all `@export("C")` functions with proper symbol visibility.

**Rationale:**
To use Simple classes from C/C++, the compiled code must be available as a shared library that can be linked into C/C++ build systems. This is the standard distribution mechanism for native libraries across all major platforms.

**Acceptance Criteria:**
1. `bin/simple build --shared --entry src/mylib.spl -o build/libmylib` produces a shared library.
2. On Linux, the output is `libmylib.so` compiled with `-shared -fPIC`.
3. On macOS, the output is `libmylib.dylib` compiled with `-dynamiclib`.
4. On Windows, the output is `mylib.dll` with a corresponding `mylib.lib` import library.
5. All `@export("C")` functions are visible in the shared library's symbol table (verifiable with `nm -D` or `dumpbin /EXPORTS`).
6. Non-exported functions are not visible in the symbol table.
7. The shared library can be linked into a C/C++ program using standard flags (`-L` + `-l` on Unix, `/LIBPATH` on MSVC).

---

### REQ-SFFI-BIDIR009: Runtime Library Mode

**Priority:** P1
**Dependencies:** REQ-SFFI-BIDIR008

**Description:**
Shared libraries built from Simple code shall include `spl_library_init()` and `spl_library_shutdown()` functions for initializing and tearing down the Simple runtime. Optionally, auto-initialization via platform-specific mechanisms (`__attribute__((constructor))` on Unix, `DllMain` on Windows) shall be supported.

**Rationale:**
The Simple runtime (GC, thread pool, etc.) must be initialized before any exported function can be called. Explicit init/shutdown functions give C/C++ consumers control over lifecycle, while auto-init provides convenience for simple use cases.

**Acceptance Criteria:**
1. Every shared library built with `--shared` exports `spl_library_init(void)` and `spl_library_shutdown(void)`.
2. Calling any `@export("C")` function before `spl_library_init()` either auto-initializes or returns a defined error (not undefined behavior).
3. `spl_library_shutdown()` cleanly releases all runtime resources (GC, thread pools, etc.).
4. Multiple calls to `spl_library_init()` are idempotent (reference-counted or guarded).
5. Multiple calls to `spl_library_shutdown()` are safe (no double-free).
6. Auto-init via `__attribute__((constructor))` is available as an opt-in build flag (`--auto-init`).
7. On Windows, `DllMain` auto-init is available as an opt-in build flag.

---

### REQ-SFFI-BIDIR010: Bitfield Support with @bits(N)

**Priority:** P3
**Dependencies:** REQ-SFFI-BIDIR005, REQ-SFFI-BIDIR006

**Description:**
The `@bits(N)` attribute on struct fields specifies explicit bit widths for FFI structs, enabling interop with hardware registers, network protocols, and other bit-packed data structures. The compiler computes exact bit layout matching C bitfield packing rules and generates matching C bitfield structs in headers.

**Rationale:**
Embedded systems and protocol implementations frequently use bitfields. Without explicit bit-width support, Simple cannot interoperate with hardware register maps, network packet headers, or existing C bitfield structs. The `@bits(N)` annotation makes the layout explicit and verifiable.

**Acceptance Criteria:**
1. `@bits(N)` can be applied to integer-type fields in an `@repr("C")` struct, where N is 1-64.
2. The compiler validates that N does not exceed the field type's width (e.g., `@bits(9)` on `u8` is an error).
3. Multiple bitfields pack into storage units following the target platform's C bitfield packing rules.
4. Generated C headers produce matching C bitfield structs:
   ```c
   struct spl_GpioRegister {
       uint8_t mode : 4;
       uint8_t output : 1;
       uint8_t input : 1;
       uint8_t speed : 2;
   };
   ```
5. `_Static_assert` verifies the total struct size matches between Simple and C.
6. Bitfield access in Simple code generates correct bit manipulation instructions (shift + mask).
7. `@bits(N)` without `@repr("C")` triggers lint rule SFFI004.

---

### REQ-SFFI-BIDIR011: Plugin Manifest for Extern Fn Registration

**Priority:** P2
**Dependencies:** None

**Description:**
A plugin manifest system (`manifest.sdn`) shall allow declaring extern function names per external library, so that the semantic analyzer accepts these functions provisionally without requiring them in the built-in runtime whitelist. This unblocks the C++ -> Simple direction of the existing three-tier SFFI pattern.

**Rationale:**
The semantic analyzer currently rejects all `extern fn` declarations that are not in the hardcoded runtime whitelist of 129 functions. This blocks the entire C++ -> Simple SFFI direction (Phase 4). A plugin manifest is the minimal change needed to make the semantic analyzer plugin-aware without requiring dynamic library loading at compile time.

**Acceptance Criteria:**
1. A `manifest.sdn` file in `~/.simple/plugins/` lists plugin libraries and their exported extern function names. Tests may override the path with `SIMPLE_PLUGIN_MANIFEST`.
2. The semantic analyzer reads the manifest before type-checking and registers listed functions as provisionally available.
3. Code using `extern fn rt_regex_new(...)` compiles successfully when `rt_regex_new` is listed in the manifest.
4. Code using an `extern fn` not in the manifest or runtime whitelist still produces a clear error.
5. The CLI provides `bin/simple plugin install <manifest.sdn>`, `bin/simple plugin list`, and `bin/simple plugin remove <name>` for manifest-managed plugins.
6. The manifest format is SDN (not JSON/YAML), consistent with Simple conventions.
7. Missing plugin `.so` files at runtime produce a clear error message with the expected library path.

---

### REQ-SFFI-BIDIR012: @export("C") on Standalone Functions

**Priority:** P0
**Dependencies:** None

**Description:**
The `@export("C")` attribute shall also be applicable to standalone (module-level) functions, exporting them with C ABI linkage and a `spl_` prefixed symbol name. This enables exporting utility functions, factory functions, and APIs that are not tied to a specific class.

**Rationale:**
Not all exported APIs are class methods. Utility functions, global configuration, version queries, and factory functions are commonly exported as standalone C functions. Supporting `@export("C")` on functions (not just classes) provides a complete export story.

**Acceptance Criteria:**
1. `@export("C")` can be applied to any module-level function definition.
2. The exported function uses `extern "C"` linkage with symbol name `spl_{functionName}`.
3. The function appears in generated C headers with the correct signature.
4. Parameters and return types are validated for C-compatibility (same rules as SFFI001).
5. The function is visible in the shared library symbol table when built with `--shared`.
6. `@export("C")` on a function with non-C-compatible parameter types produces lint error SFFI001.
7. Overloaded functions (same name, different parameter types) produce a clear error — C does not support overloading.

---

## Traceability Matrix

| Requirement | Direction | Phase | Key Files |
|-------------|-----------|-------|-----------|
| REQ-SFFI-BIDIR001 | A: Simple -> C/C++ | A1 | `src/compiler/35.semantics/resolve.spl` |
| REQ-SFFI-BIDIR002 | A: Simple -> C/C++ | A2 | `src/compiler/70.backend/backend/c_backend_translate.spl` |
| REQ-SFFI-BIDIR003 | A: Simple -> C/C++ | A4 | `src/compiler/90.tools/header_gen/c_header.spl` (new) |
| REQ-SFFI-BIDIR004 | A: Simple -> C/C++ | A5 | `src/compiler/90.tools/header_gen/cpp_header.spl` (new) |
| REQ-SFFI-BIDIR005 | C: Layout Safety | C1 | `src/compiler/35.semantics/resolve.spl` |
| REQ-SFFI-BIDIR006 | C: Layout Safety | C2 | `src/compiler/90.tools/header_gen/layout_verifier.spl` (new) |
| REQ-SFFI-BIDIR007 | C: Layout Safety | C3 | `src/compiler/35.semantics/lint/` (new rules) |
| REQ-SFFI-BIDIR008 | A: Simple -> C/C++ | A6 | `src/compiler/80.driver/`, linker wrapper |
| REQ-SFFI-BIDIR009 | A: Simple -> C/C++ | A6 | `src/runtime/runtime.h`, `src/runtime/runtime.c` |
| REQ-SFFI-BIDIR010 | C: Layout Safety | C5 | `src/compiler/70.backend/backend/common/type_mapper.spl` |
| REQ-SFFI-BIDIR011 | B: C++ -> Simple | B1 | `src/compiler/35.semantics/`, `src/app/plugin/` |
| REQ-SFFI-BIDIR012 | A: Simple -> C/C++ | A1 | `src/compiler/35.semantics/resolve.spl` |

## Priority Summary

| Priority | Requirements | Scope |
|----------|-------------|-------|
| **P0** | BIDIR001, BIDIR002, BIDIR005, BIDIR006, BIDIR007, BIDIR012 | Core export, layout safety, lint rules |
| **P1** | BIDIR003, BIDIR004, BIDIR008, BIDIR009 | Header generation, shared library build |
| **P2** | BIDIR011 | Plugin manifest (unblocks C++ -> Simple) |
| **P3** | BIDIR010 | Bitfield support |
