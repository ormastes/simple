# SFFI Bidirectional Interop Support Matrix

**Date:** 2026-04-04
**Status:** Active
**Version:** 1.0
**Related Requirements:** [sffi_bidirectional_interop.md](/doc/02_requirements/feature/usage/sffi_bidirectional_interop.md)
**Related Design:** [sffi_bidirectional_interop.md](/doc/05_design/sffi_bidirectional_interop.md)
**Related Architecture:** [sffi_bidirectional_interop.md](/doc/04_architecture/sffi_bidirectional_interop.md)

---

## 1. Feature x Direction x Language Matrix

Legend:
- **Supported** -- Implemented and tested
- **Partial (note)** -- Partially implemented with stated limitation
- **Planned (WS)** -- Planned for a specific workstream
- **Excluded (reason)** -- Explicitly out of scope with justification

| Feature | Simple->C (Dir A) | Simple->C++ (Dir A) | C->Simple (Dir B) | C++->Simple (Dir B) | Compiled Mode | Interpreter Mode |
|---|---|---|---|---|---|---|
| **Class export** | Supported | Supported (RAII wrapper) | Planned (WS4: plugin manifest) | Planned (WS4: plugin manifest + wrapper_spec) | Supported | Partial (header gen + lint only) |
| **Function export** | Supported | Supported (via C header `extern "C"`) | Planned (WS4: manifest registration) | Planned (WS4: manifest registration) | Supported | Partial (header gen + lint only) |
| **Struct by-value pass** | Supported (`@repr("C")` required) | Supported (`@repr("C")` required) | Supported (`@repr("C")` required) | Supported (`@repr("C")` required) | Supported | Partial (lint validation only) |
| **Callback / function pointer** | Partial (C function pointers, no captures) | Partial (C function pointers, no captures) | Planned (WS4: extern fn registration) | Planned (WS4: extern fn registration) | Supported | Excluded (requires compiled runtime) |
| **Error conversion (Result->error)** | Partial (design deferred: `spl_error_t*` out-param or `spl_last_error()` TLS) | Partial (design deferred: same as C) | Planned (WS4) | Planned (WS4) | Supported | Excluded (requires compiled runtime) |
| **Handle lifecycle (create/use/destroy)** | Supported (opaque handle pattern) | Supported (RAII via C++ wrapper) | Planned (WS4: dlopen + handle import) | Planned (WS4: dlopen + handle import) | Supported | Excluded (requires compiled runtime) |
| **Array / collection pass** | Partial (opaque `spl_array_t` handle) | Partial (`spl::Array<T>` wrapper planned) | Planned (WS4) | Planned (WS4) | Supported | Excluded (requires compiled runtime) |
| **String / text pass** | Supported (`const char*` UTF-8) | Supported (`const char*` or `std::string_view`) | Supported (`const char*` UTF-8) | Supported (`const char*` UTF-8) | Supported | Partial (lint SFFI002 warns on `text` fields) |
| **Optional / nullable** | Partial (`T` + bool flag, or nullable pointer) | Partial (`std::optional<T>` mapping planned) | Planned (WS4) | Planned (WS4) | Supported | Excluded (requires compiled runtime) |
| **Bitfield support (`@bits(N)`)** | Planned (WS-C5, P3) | Planned (WS-C5, P3) | Planned (WS-C5, P3) | Planned (WS-C5, P3) | Planned (WS-C5) | Partial (lint SFFI004 validates annotations) |

---

## 2. Type Mapping Table

All type mappings are implemented in `CTypeMapper` at `src/compiler/70.backend/backend/common/type_mapper.spl`.

| Simple Type | C Type | C++ Type | Direction A (Simple->C/C++) | Direction B (C/C++->Simple) | Proof Status |
|---|---|---|---|---|---|
| `i8` | `int8_t` | `int8_t` | Supported | Supported | Tested (unit + integration) |
| `i16` | `int16_t` | `int16_t` | Supported | Supported | Tested (unit + integration) |
| `i32` | `int32_t` | `int32_t` | Supported | Supported | Tested (unit + integration) |
| `i64` | `int64_t` | `int64_t` | Supported | Supported | Tested (unit + integration) |
| `u8` | `uint8_t` | `uint8_t` | Supported | Supported | Tested (unit + integration) |
| `u16` | `uint16_t` | `uint16_t` | Supported | Supported | Tested (unit + integration) |
| `u32` | `uint32_t` | `uint32_t` | Supported | Supported | Tested (unit + integration) |
| `u64` | `uint64_t` | `uint64_t` | Supported | Supported | Tested (unit + integration) |
| `f32` | `float` | `float` | Supported | Supported | Tested (unit + integration) |
| `f64` | `double` | `double` | Supported | Supported | Tested (unit + integration) |
| `bool` | `bool` (`<stdbool.h>`) | `bool` | Supported | Supported | Tested (unit + integration) |
| `text` | `const char*` (UTF-8) | `std::string_view` or `const char*` | Supported (SFFI002 warns) | Supported | Tested (with lint warning) |
| `Option<T>` | `T` + `bool` flag, or nullable pointer | `std::optional<T>` | Partial (nullable pointer for handle types) | Planned | Design specified |
| `[T]` (array) | `spl_array_t` (opaque handle) | `spl::Array<T>` | Partial (opaque only) | Planned | Design specified |
| Opaque handle (`@export("C")` class) | `spl_ClassName_t` (`typedef struct spl_X* spl_X_t`) | `spl::ClassName` (RAII wrapper) | Supported | Planned (WS4: dlopen) | Tested (integration) |
| Function pointer | `ReturnType (*)(ParamTypes)` | `ReturnType (*)(ParamTypes)` | Partial (no captures) | Planned | Design specified |

---

## 3. Known Exclusions

| Exclusion | Reason | Workaround |
|---|---|---|
| **Generics across FFI boundary** | Type erasure is not safe for C ABI; monomorphized types have mangled names incompatible with stable C symbols. SFFI001 lint rule rejects generic fields in `@export("C")` classes. | Monomorphize before export: create a concrete type alias (e.g., `type IntList = List<Int>`) and export the concrete type. |
| **Closures with captures** | Captured variables interact with Simple's GC; passing a closure across FFI creates dangling references if the GC collects captured objects while C holds the closure pointer. | Use plain function pointers (`fn` without captures) for callbacks. Pass context via an explicit `void* user_data` parameter. |
| **Trait objects across FFI** | Trait object vtable layout is Simple-internal and not C-ABI-compatible. Exposing vtable pointers would create a fragile binary interface. | Export concrete types. If polymorphism is needed, use the opaque handle pattern with a dispatch function on the Simple side. |
| **Runtime GC interaction from C callbacks** | C code calling back into Simple may trigger GC at unsafe points. The GC cannot scan C stack frames for root pointers, risking use-after-move. | Ensure all Simple objects accessed from C callbacks are pinned or reference-counted. Design GC-safe callback trampolines (future work). |
| **Interpreter mode for Direction B runtime loading** | Direction B requires `dlopen`/`LoadLibrary` to load C/C++ shared libraries at runtime. The interpreter does not have a compiled native runtime to host loaded libraries. | Use compiled mode for Direction B. Interpreter mode supports Direction A lint validation and header generation only. |

---

## 4. Runtime Mode Support

| Capability | Compiled Mode | Interpreter Mode |
|---|---|---|
| **Direction A: @export("C") validation** | Supported | Supported |
| **Direction A: C ABI function generation** | Supported | N/A (no codegen) |
| **Direction A: C header generation (--emit-header)** | Supported | Supported |
| **Direction A: C++ header generation (--emit-cxx-header)** | Supported | Supported |
| **Direction A: Shared library build (--shared)** | Supported | N/A (no codegen) |
| **Direction A: Library init/shutdown** | Supported | N/A (no runtime) |
| **Direction B: Plugin manifest loading** | Supported | Supported (validation only) |
| **Direction B: extern fn registration** | Supported | Supported (type-check only) |
| **Direction B: dlopen runtime loading** | Supported | Excluded (compiled-only for v1) |
| **Direction B: Dynamic dispatch to C++ methods** | Supported | Excluded (compiled-only for v1) |
| **Direction C: @repr("C") layout enforcement** | Supported | Supported |
| **Direction C: _Static_assert generation** | Supported | Supported (in generated headers) |
| **Direction C: SFFI lint rules (SFFI001-005)** | Supported | Supported |
| **Direction C: @bits(N) bitfield validation** | Planned (P3) | Planned (P3, lint only) |

---

## 5. Requirement Traceability

| Requirement | Description | Matrix Cell(s) | Status | Priority |
|---|---|---|---|---|
| **REQ-SFFI-BIDIR001** | `@export("C")` attribute on classes | Class export (Dir A, all columns) | Implemented | P0 |
| **REQ-SFFI-BIDIR002** | C ABI function generation | Function export + Handle lifecycle (Dir A: Simple->C) | Implemented | P0 |
| **REQ-SFFI-BIDIR003** | C header generation (`.h`) | Class export + Function export (Dir A: Simple->C), Compiled + Interpreter (header gen) | Implemented | P1 |
| **REQ-SFFI-BIDIR004** | C++ wrapper generation (`.hpp`) | Class export + Function export (Dir A: Simple->C++), Compiled + Interpreter (header gen) | Implemented | P1 |
| **REQ-SFFI-BIDIR005** | `@repr("C")` attribute | Struct by-value pass (all directions) | Implemented | P0 |
| **REQ-SFFI-BIDIR006** | Compile-time layout verification (`_Static_assert`) | Struct by-value pass (Dir A: Simple->C, Simple->C++), Compiled + Interpreter (header gen) | Implemented | P0 |
| **REQ-SFFI-BIDIR007** | SFFI lint rules (SFFI001-005) | All rows where lint applies: Class export, Function export, Struct by-value, Bitfield, String/text | Implemented | P0 |
| **REQ-SFFI-BIDIR008** | Shared library build mode (`--shared`) | Class export + Function export + Handle lifecycle (Dir A), Compiled mode only | Implemented | P1 |
| **REQ-SFFI-BIDIR009** | Runtime library mode (`spl_library_init/shutdown`) | Handle lifecycle (Dir A: Simple->C, Simple->C++), Compiled mode only | Implemented | P1 |
| **REQ-SFFI-BIDIR010** | Bitfield support (`@bits(N)`) | Bitfield support (all directions) | Planned (P3, WS-C5) | P3 |
| **REQ-SFFI-BIDIR011** | Plugin manifest for extern fn registration | Class export + Function export + Callback + Handle lifecycle (Dir B: C->Simple, C++->Simple) | Planned (WS4) | P2 |
| **REQ-SFFI-BIDIR012** | `@export("C")` on standalone functions | Function export (Dir A: Simple->C, Simple->C++) | Implemented | P0 |

---

## 6. Implementation Phase Mapping

Each requirement maps to an architecture phase (from the 9-stage pipeline):

| Phase | Stage | Requirements | Status |
|---|---|---|---|
| **Phase 0: Existing** | Parsing, CTypeMapper, callconv | (prerequisites) | Complete |
| **Phase 1: Foundation (P0)** | Attribute extraction, HIR, Semantic validation, SFFI lint | REQ-SFFI-BIDIR001, 005, 007, 012 | Complete |
| **Phase 2: Code Generation (P0)** | MIR export metadata, C backend wrappers, LLVM export | REQ-SFFI-BIDIR002 | Complete |
| **Phase 3: Tooling (P1)** | Header gen, layout verifier, shared lib linker, driver CLI | REQ-SFFI-BIDIR003, 004, 006, 008, 009 | Complete |
| **Phase 4: C++ -> Simple (P2)** | Plugin manifest, wrapper gen, dynamic loading | REQ-SFFI-BIDIR011 | Planned |
| **Phase 5: Bitfields (P3)** | `@bits(N)` annotation, bit layout computation | REQ-SFFI-BIDIR010 | Planned |

---

## 7. Key File Inventory

| Component | File Path | Role |
|---|---|---|
| CTypeMapper | `src/compiler/70.backend/backend/common/type_mapper.spl` | Simple-to-C type mapping |
| Calling convention | `src/compiler/70.backend/callconv_bridge.spl` | `@callconv("C")` support |
| C backend | `src/compiler/70.backend/backend/c_backend_translate.spl` | `extern "C"` wrapper emission |
| Linker wrapper | `src/compiler/70.backend/linker/linker_wrapper.spl` | `--shared` build mode |
| Attribute parsing | `src/compiler/00.common/attributes.spl` | `@export("C")`, `@repr("C")`, `@bits(N)` extraction |
| HIR definitions | `src/compiler/20.hir/hir_definitions.spl` | Export + layout metadata on HirClass |
| Semantic resolve | `src/compiler/35.semantics/resolve.spl` | Export validation |
| SFFI lint | `src/compiler/35.semantics/lint/sffi_lint.spl` | SFFI001-005 rules |
| Header gen (C) | `src/compiler/90.tools/header_gen/c_header.spl` | `.h` emitter |
| Header gen (C++) | `src/compiler/90.tools/header_gen/cpp_header.spl` | `.hpp` RAII wrapper emitter |
| Layout verifier | `src/compiler/90.tools/header_gen/layout_verifier.spl` | `_Static_assert` generation |
| Wrapper spec parser | `src/app/wrapper_gen/spec_parser.spl` | `.wrapper_spec` -> manifest (Dir B) |
| LLVM entry point | `src/compiler/70.backend/backend/entry_point.spl` | `dso_local` export linkage |
| Driver API | `src/compiler/80.driver/driver_api.spl` | `--shared`, `--emit-header`, `--emit-cxx-header` flags |
