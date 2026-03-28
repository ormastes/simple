# NFR -- SFFI Bidirectional Class Interop

**Related requirements:** [doc/02_requirements/feature/usage/sffi_bidirectional_interop.md](../feature/usage/sffi_bidirectional_interop.md)
**Related design:** [doc/05_design/sffi_external_library_pattern.md](../../05_design/sffi_external_library_pattern.md), [doc/05_design/cpp_wrapper_generator_design.md](../../05_design/cpp_wrapper_generator_design.md)
**Related research:** [doc/01_research/local/sffi_dynamic_loading_2026-02-21.md](../../01_research/local/sffi_dynamic_loading_2026-02-21.md)

---

## NFR-SFFI-001: Cross-Platform Support

**Category:** Portability

All SFFI bidirectional interop features shall work across the three supported platforms:

- **Linux x86_64:** `.so` shared libraries, `dlopen`/`dlsym` for dynamic loading, GCC and Clang toolchains
- **macOS ARM64/x86_64:** `.dylib` shared libraries, `dlopen`/`dlsym`, Apple Clang toolchain, universal binary support
- **Windows x86_64:** `.dll` shared libraries with `.lib` import libraries, `LoadLibrary`/`GetProcAddress`, MSVC (`cl.exe`/`link.exe`) and MinGW (`gcc`/`ld`) toolchains

### Verification

| Check | Method | Pass Criteria |
|-------|--------|---------------|
| Linux `.so` generation | CI build + `nm -D` symbol check | All `@export("C")` symbols visible |
| macOS `.dylib` generation | CI build + `nm -gU` symbol check | All `@export("C")` symbols visible |
| Windows `.dll` generation | CI build + `dumpbin /EXPORTS` | All `@export("C")` symbols visible |
| Generated `.h` compiles on all platforms | Cross-compile with GCC, Clang, MSVC | Zero warnings with `-Wall -Wextra` / `/W4` |
| Generated `.hpp` compiles on all platforms | Cross-compile with g++, clang++, MSVC | Zero warnings with C++17 mode |
| Plugin manifest loading | Unit tests on all 3 platforms | Consistent behavior |

---

## NFR-SFFI-002: ABI Stability

**Category:** Reliability

Struct layout for `@repr("C")` types must be **deterministic and reproducible** across compilations:

- Given the same source code and target triple, the Simple compiler shall produce identical field offsets, struct sizes, and padding bytes on every compilation.
- Layout computation shall follow the System V AMD64 ABI (Linux/macOS) or Microsoft x64 ABI (Windows) depending on the target.
- The compiler shall not reorder, pad, or align `@repr("C")` fields differently from what the target C compiler would produce.
- Generated `_Static_assert` layout checks (REQ-SFFI-BIDIR006) shall pass with GCC >= 10, Clang >= 12, and MSVC >= 19.29 on all supported platforms.

### Verification

| Check | Method | Pass Criteria |
|-------|--------|---------------|
| Deterministic layout | Compile same source twice, compare layout JSON | Byte-identical output |
| Matches C compiler | Compile `@repr("C")` struct + equivalent C struct, compare `sizeof`/`offsetof` | All values equal |
| `_Static_assert` pass | Compile generated header with GCC, Clang, MSVC | Zero assertion failures |
| Cross-compilation | Compile for x86_64-linux from macOS host, verify layout | Matches native Linux compilation |

---

## NFR-SFFI-003: Zero Overhead

**Category:** Performance

Exported functions shall have **no more than one level of indirection** compared to a hand-written C equivalent:

- **Opaque handle pattern:** One pointer dereference to access the underlying Simple object from a handle (acceptable overhead).
- **Method dispatch:** Direct function call, no vtable lookup, no dynamic dispatch for exported methods.
- **`@repr("C")` structs passed by value:** Zero overhead -- identical memory layout, no marshalling or copying beyond what C would do.
- **String parameters:** One UTF-8 validation + null-terminator copy per string argument (unavoidable, not counted as "overhead").
- **`spl_library_init()`:** One-time cost, amortized to zero over library lifetime.

### Verification

| Check | Method | Pass Criteria |
|-------|--------|---------------|
| Handle dereference | Inspect generated assembly for exported method | Single `mov` to load object pointer from handle |
| No vtable | Inspect generated assembly | Direct `call` instruction, no indirect jump |
| Struct pass-by-value | Compare assembly of Simple export vs hand-written C | Identical register/stack usage |
| Benchmark: method call | 10M calls to exported method from C | < 5% overhead vs native C function call |
| Benchmark: struct access | 10M reads of `@repr("C")` struct field from C | < 1% overhead vs native C struct access |

---

## NFR-SFFI-004: Compile-Time Safety

**Category:** Safety

All layout mismatches and type incompatibilities shall be caught **before runtime**:

- **SFFI lint rules (SFFI001-SFFI005):** Run during `bin/simple build` and `bin/simple build lint`, producing errors or warnings before code generation.
- **`_Static_assert` in generated headers:** Catch layout mismatches when the C/C++ consumer compiles the header, before linking.
- **Plugin manifest validation:** Missing or invalid manifests produce clear compile-time errors, not runtime crashes.
- **No silent degradation:** There shall be no code path where a layout mismatch, type incompatibility, or missing symbol results in undefined behavior at runtime without a prior compile-time or link-time diagnostic.

### Verification

| Check | Method | Pass Criteria |
|-------|--------|---------------|
| Non-C type in `@export("C")` | Compile class with closure field | SFFI001 error at compile time |
| Missing `@repr("C")` | Pass struct by value in extern fn | SFFI003 error at compile time |
| Layout mismatch | Modify struct in Simple but not C, compile | `_Static_assert` failure in C compiler |
| Missing plugin `.so` | Import extern fn from unregistered plugin | Clear compile-time error with library path |
| Bitfield width overflow | `@bits(9)` on `u8` field | Compile-time error |
| All diagnostic messages | Review all SFFI error/warning messages | Each message names the offending item, expected vs actual, and suggests a fix |

---

## Traceability

| NFR | Related Functional Requirements |
|-----|--------------------------------|
| NFR-SFFI-001 | REQ-SFFI-BIDIR003, BIDIR004, BIDIR008, BIDIR009, BIDIR011 |
| NFR-SFFI-002 | REQ-SFFI-BIDIR005, BIDIR006, BIDIR010 |
| NFR-SFFI-003 | REQ-SFFI-BIDIR002, BIDIR005 |
| NFR-SFFI-004 | REQ-SFFI-BIDIR006, BIDIR007, BIDIR010, BIDIR011 |
