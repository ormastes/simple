# Architecture: SFFI Bidirectional Class Interop

**Related requirements:**
- [doc/02_requirements/feature/usage/sffi_bidirectional_interop.md](../02_requirements/feature/usage/sffi_bidirectional_interop.md) (REQ-SFFI-BIDIR001–012)
- [doc/02_requirements/nfr/sffi_bidirectional_interop.md](../02_requirements/nfr/sffi_bidirectional_interop.md) (NFR-SFFI-001–004)

**Related design:** [doc/05_design/sffi_bidirectional_interop.md](../05_design/sffi_bidirectional_interop.md)

**Existing designs:**
- [doc/05_design/sffi_external_library_pattern.md](../05_design/sffi_external_library_pattern.md)
- [doc/05_design/cpp_wrapper_generator_design.md](../05_design/cpp_wrapper_generator_design.md)
- [doc/05_design/phase4_sffi_implementation_plan.md](../05_design/phase4_sffi_implementation_plan.md)

---

## 1. Overview

This document describes the architecture for bidirectional class-level interop between Simple and C/C++. The feature enables:

- **Direction A (Simple -> C/C++):** Write a class in Simple, annotate with `@export("C")`, compiler generates C ABI wrappers, C headers, and C++ wrapper headers.
- **Direction B (C++ -> Simple):** Existing 3-tier SFFI (`.wrapper_spec` -> generated manifest -> `extern fn` -> Simple class). Implemented via manifest-backed extern registration and dynamic library lookup.
- **Direction C (Layout Verification):** `@repr("C")` layout enforcement, compile-time `_Static_assert` generation, SFFI lint rules.

---

## 2. Component Diagram

```
                          Simple Source (.spl)
                               |
                     +---------v---------+
                     |   10.frontend     |
                     |   Parser          |
                     |   (parser_types)  |
                     +--------+----------+
                              |  AST with Attribute nodes
                              |  (@export("C"), @repr("C"), @bits(N))
                     +--------v----------+
                     |   00.common       |
                     |   attributes.spl  |
                     |   parse_layout_   |
                     |   attrs()         |
                     |   parse_function_ |
                     |   attrs()         |
                     +--------+----------+
                              |  LayoutAttr, FunctionAttr, ExportAttr (NEW)
                     +--------v----------+
                     |   20.hir          |
                     |   hir_lowering/   |
                     |   items.spl       |
                     |   hir_definitions |
                     +--------+----------+
                              |  HirClass with layout_attr + export_attr (NEW)
                     +--------v----------+
                     |   35.semantics    |
                     |   resolve.spl     |
                     |   lint/sffi_lint  | <-- NEW
                     +--------+----------+
                              |  Validated exports, SFFI001-005 diagnostics
                     +--------v----------+
                     |   50.mir          |
                     |   mir_data.spl    |
                     |   (MirFunction    |
                     |    export tags)   |
                     +--------+----------+
                              |  MIR with export metadata
              +---------------+---------------+
              |                               |
     +--------v----------+          +--------v----------+
     |   70.backend       |          |   70.backend       |
     |   C backend        |          |   LLVM backend     |
     |   c_backend_       |          |   entry_point.spl  |
     |   translate.spl    |          |   (dso_local        |
     |   (extern "C"      |          |    linkage)         |
     |    wrappers)       |          +--------+----------+
     +--------+-----------+                   |
              |                               |
     +--------v----------+          +--------v----------+
     |   70.backend       |          |   70.backend       |
     |   linker/          |          |   linker/          |
     |   linker_wrapper   |          |   linker_wrapper   |
     |   (--shared mode)  |          |   (--shared mode)  |
     +--------+-----------+          +--------+----------+
              |                               |
              +---------------+---------------+
                              |
                     +--------v----------+
                     |   90.tools        |
                     |   header_gen/     | <-- NEW
                     |   c_header.spl    |
                     |   cpp_header.spl  |
                     |   layout_verifier |
                     +--------+----------+
                              |
                    +---------+---------+
                    |         |         |
                 .h file   .hpp file   .so/.dylib/.dll
```

---

## 3. Data Flow: @export("C") Through the Pipeline

### Stage 1: Parsing (10.frontend)

The parser reads `@export("C")` as an `Attribute` node attached to a `Class` or `Function` AST node.

**Existing infrastructure:**
- `Attribute` struct: `src/compiler/10.frontend/parser_types.spl` — `{ name: text, args: [Expr], span: Span }`
- `Class` struct: `src/compiler/10.frontend/parser_types.spl` — has `attributes: [Attribute]` field

No parser changes needed. `@export("C")` is already a valid attribute syntactically.

### Stage 2: Attribute Extraction (00.common)

The attribute parsing functions extract structured data from raw `Attribute` nodes.

**Existing infrastructure:**
- `parse_layout_attrs()`: `src/compiler/00.common/attributes.spl` — handles `@repr("C")`, `@repr("packed")`, `@align(N)`
- `parse_function_attrs()`: `src/compiler/00.common/attributes.spl` — handles `@entry`, `@naked`, `@interrupt`, etc.
- `LayoutAttr` struct with `LayoutKind.C`: already models C-compatible layout
- `FunctionAttr` struct: per-function boolean flags

**New component:** `parse_export_attrs()` function and `ExportAttr` struct, added to `attributes.spl`.

### Stage 3: HIR Lowering (20.hir)

AST classes are lowered to `HirClass` with layout and export metadata.

**Existing infrastructure:**
- `HirClass`: `src/compiler/20.hir/hir_definitions.spl` — has `has_layout_attr: bool`, `layout_attr: LayoutAttr`
- Class lowering: `src/compiler/20.hir/hir_lowering/items.spl` — calls `parse_layout_attrs()`

**New fields:** `has_export_attr: bool`, `export_attr: ExportAttr` on `HirClass`.

### Stage 4: Semantic Validation (35.semantics)

The semantic pass validates export constraints and runs SFFI lint rules.

**Existing infrastructure:**
- Lint pattern: `src/compiler/35.semantics/lint/remote_exec_lint.spl` — `LintWarning` struct + check functions
- Semantic resolve: `src/compiler/35.semantics/resolve.spl`

**New components:**
- Export validation in `resolve.spl`: C-compatible types only, no generics, public only
- `src/compiler/35.semantics/lint/sffi_lint.spl` (NEW): SFFI001–SFFI005 rules

### Stage 5: MIR (50.mir)

MIR functions carry export metadata tags.

**Existing infrastructure:**
- `MirFunction`: `src/compiler/50.mir/mir_data.spl`

**New fields:** Export flag + export name on `MirFunction`.

### Stage 6: Code Generation (70.backend)

The backend emits `extern "C"` wrapper functions for exported classes.

**Existing infrastructure:**
- C backend: `src/compiler/70.backend/backend/c_backend_translate.spl` — `MirToC` class, `emit_type_definitions()`, `translate_module()`
- LLVM entry point: `src/compiler/70.backend/backend/entry_point.spl` — `generate_entry_point_ir()`
- `CTypeMapper`: `src/compiler/70.backend/backend/common/type_mapper.spl` — Simple-to-C type mapping
- Calling convention: `src/compiler/70.backend/callconv_bridge.spl` — `callconv_from_string("C")`

**New methods on MirToC:**
- `emit_export_wrappers()` — generates `extern "C"` functions for each exported class method
- `emit_library_init()` — generates `spl_library_init()` / `spl_library_shutdown()`

### Stage 7: Linking (70.backend/linker)

The linker wrapper supports `--shared` output mode.

**Existing infrastructure:**
- `link_to_native()`: `src/compiler/70.backend/linker/linker_wrapper.spl` — platform-detected native binary
- `LinkerConfig` struct with platform-aware flag selection

**New mode:** `link_to_shared()` — `-shared -fPIC` (Linux), `-dynamiclib` (macOS), `/DLL` (Windows)

### Stage 8: Header Generation (90.tools — NEW)

A new tool scans MIR for exported classes and emits headers.

**New components:**
- `src/compiler/90.tools/header_gen/mod.spl` — entry point
- `src/compiler/90.tools/header_gen/c_header.spl` — `.h` emitter with `_Static_assert` layout checks
- `src/compiler/90.tools/header_gen/cpp_header.spl` — `.hpp` C++ wrapper class emitter
- `src/compiler/90.tools/header_gen/layout_verifier.spl` — struct layout computation + verification

### Stage 9: Driver Integration (80.driver)

The driver adds new build modes.

**Existing infrastructure:**
- `src/compiler/80.driver/driver_api.spl` — `compile_file()`, `aot_file()`, `aot_c_file()`

**New CLI flags:**
- `--shared` — produce shared library instead of executable
- `--emit-header` — generate `.h` file
- `--emit-cxx-header` — generate `.hpp` file

---

## 4. Integration Points with Existing Components

| Existing Component | Integration | Change Type |
|--------------------|-------------|-------------|
| `Attribute` (parser_types.spl) | Source of `@export("C")` | No change (already parsed) |
| `parse_layout_attrs()` (attributes.spl) | `@repr("C")` extraction | No change (already works) |
| `parse_function_attrs()` (attributes.spl) | Template for `parse_export_attrs()` | Add sibling function |
| `LayoutKind.C` (type_layout.spl) | C layout computation for exported structs | No change (already works) |
| `compute_c_abi_layout()` (type_layout.spl) | Field offset computation for `_Static_assert` | Extend with offset export |
| `HirClass` (hir_definitions.spl) | Carries export metadata through pipeline | Add 2 fields |
| `HirField` (hir_definitions.spl) | Bitfield annotation storage | Add `has_bits_attr`, `bits_width` |
| `CTypeMapper` (type_mapper.spl) | Type mapping for header generation | No change (reuse as-is) |
| `callconv_from_string("C")` (callconv_bridge.spl) | Calling convention for export wrappers | No change (reuse as-is) |
| `MirToC` (c_backend_translate.spl) | Export wrapper code generation | Add methods |
| `generate_entry_point_ir()` (entry_point.spl) | Library init/shutdown for shared libs | Add library mode |
| `link_to_native()` (linker_wrapper.spl) | Shared library output | Add shared mode |
| `LintWarning` (remote_exec_lint.spl) | Pattern for SFFI lint warnings | Follow same pattern |
| `driver_api.spl` | New build modes | Add flags |

---

## 5. New Components

### 5.1 ExportAttr (attributes.spl)

```
ExportAttr
    is_export_c: bool
    export_name: text?    # Custom C symbol name (nil = auto-generate)
```

Parsed by new `parse_export_attrs()` function following the same pattern as `parse_function_attrs()` and `parse_layout_attrs()`.

### 5.2 SFFI Lint (35.semantics/lint/sffi_lint.spl)

Five lint rules following the `remote_exec_lint.spl` pattern:

| Rule | Severity | Check |
|------|----------|-------|
| SFFI001 | ERROR | Non-C-compatible field type in `@export("C")` class |
| SFFI002 | WARNING | `text` field in `@export("C")` class (pointer, needs marshalling) |
| SFFI003 | ERROR | Struct by-value across FFI without `@repr("C")` |
| SFFI004 | ERROR | Bitfield in FFI struct without `@bits(N)` |
| SFFI005 | WARNING | Platform-dependent type size in FFI struct |

### 5.3 Header Generator (90.tools/header_gen/)

| File | Purpose |
|------|---------|
| `mod.spl` | Entry point, scans MIR for exported classes/functions |
| `c_header.spl` | Emits `.h` with opaque handles, `extern "C"` declarations, `_Static_assert` |
| `cpp_header.spl` | Emits `.hpp` with RAII wrapper classes (move-only, handle-delegating) |
| `layout_verifier.spl` | Computes field offsets using `type_layout.spl`, emits verification constants |

### 5.4 Export Wrapper Generation (c_backend_translate.spl)

New methods on `MirToC`:
- `emit_export_wrappers(module: MirModule)` — iterates exported classes, emits `extern "C"` functions
- `emit_library_init()` — emits `spl_library_init()` / `spl_library_shutdown()`
- `emit_opaque_handle_typedef(class_name: text)` — emits `typedef struct spl_X* spl_X_t`

### 5.5 Shared Library Linker Mode (linker_wrapper.spl)

New `link_to_shared()` function:
- Linux: `-shared -fPIC -Wl,--version-script=exports.map`
- macOS: `-dynamiclib -Wl,-exported_symbols_list,exports.txt`
- Windows: `/DLL /DEF:exports.def`

---

## 6. Cross-Cutting Concerns

### 6.1 Platform Differences

| Concern | Linux | macOS | Windows |
|---------|-------|-------|---------|
| Shared lib extension | `.so` | `.dylib` | `.dll` |
| Import library | Not needed | Not needed | `.lib` required |
| PIC requirement | `-fPIC` | Default PIC | N/A (PE format) |
| Symbol visibility | `-fvisibility=hidden` + `__attribute__((visibility("default")))` | Same | `__declspec(dllexport)` |
| Auto-init | `__attribute__((constructor))` | Same | `DllMain` |
| Linker flags | `-shared` | `-dynamiclib` | `/DLL` |

### 6.2 ABI Stability

- **Opaque handle pattern** ensures binary compatibility: internal class layout can change without breaking C consumers.
- **`_Static_assert`** in generated headers catches layout mismatches at C compile time.
- Runtime layout verification remains a future extension; the current implementation relies on generated compile-time layout assertions in C and C++ headers.
- **`@repr("C")`** on value-type structs guarantees deterministic layout matching C rules.

### 6.3 Symbol Naming Convention

All exported symbols use the `spl_` prefix to avoid namespace collisions:

| Simple Entity | C Symbol |
|---------------|----------|
| Class `Calculator` constructor | `spl_Calculator_create(...)` |
| Class `Calculator` method `add` | `spl_Calculator_add(handle, ...)` |
| Class `Calculator` destructor | `spl_Calculator_destroy(handle)` |
| Standalone function `version` | `spl_version()` |
| Library init | `spl_library_init()` |
| Library shutdown | `spl_library_shutdown()` |

### 6.4 Thread Safety

- `spl_library_init()` uses a guarded library state flag for idempotent initialization, with constructor / `DllMain` auto-init hooks in shared-library builds.
- Handle-based API is inherently thread-safe if consumers don't share handles across threads without synchronization.
- `me` (mutable) methods on shared handles require external synchronization — documented in generated headers.

### 6.5 Error Handling

- Simple uses `Result<T, E>` + `?` operator; C has no equivalent.
- Exported functions returning `Result<T, E>` are mapped to:
  - Return value: `T` (success case)
  - Error output parameter: `spl_error_t* err` (nullable, set on failure)
  - Or: return `T` with sentinel value + `spl_last_error()` thread-local (simpler API)
- Design decision deferred to detailed design document.

---

## 7. Dependency Graph (Build Order)

```
Phase 0: No changes needed
  - Attribute (parser_types.spl)     -- already works
  - LayoutKind.C (type_layout.spl)   -- already works
  - CTypeMapper (type_mapper.spl)    -- already works
  - callconv_bridge.spl              -- already works

Phase 1: Foundation (P0)
  1. ExportAttr + parse_export_attrs()     -- attributes.spl
  2. HirClass.export_attr                  -- hir_definitions.spl
  3. HIR lowering for export               -- hir_lowering/items.spl
  4. Semantic validation                   -- resolve.spl
  5. SFFI lint rules                       -- lint/sffi_lint.spl (NEW)

Phase 2: Code Generation (P0)
  6. MirFunction export metadata           -- mir_data.spl
  7. emit_export_wrappers()                -- c_backend_translate.spl
  8. LLVM dso_local export                 -- entry_point.spl

Phase 3: Tooling (P1)
  9. Header generator                      -- 90.tools/header_gen/ (NEW)
  10. Layout verifier with _Static_assert  -- header_gen/layout_verifier.spl (NEW)
  11. Shared library linker mode           -- linker_wrapper.spl
  12. Driver CLI flags                     -- driver_api.spl

Phase 4: C++ -> Simple (P2)
  13. Plugin manifest                      -- 35.semantics/
  14. Wrapper generator fixes              -- app/wrapper_gen/
  15. Dynamic library loading              -- runtime/
```

---

## 8. Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| ABI differences between compilers (MSVC vs GCC padding) | Silent data corruption | `_Static_assert` / `static_assert` in generated headers |
| Generic types in exported classes | Compile error or mangled symbols | Reject generics in SFFI001 lint rule |
| GC interaction with C consumers | Use-after-free if C holds stale handle | Reference counting on handles, weak handle support |
| Windows DLL complexity (import lib, DllMain) | Platform-specific build failures | Comprehensive CI on Windows (MSVC + MinGW) |
| Thread safety of runtime init | Race condition on first call | Guarded init state + auto-init hooks; tighten with `call_once` if lifecycle complexity grows |
