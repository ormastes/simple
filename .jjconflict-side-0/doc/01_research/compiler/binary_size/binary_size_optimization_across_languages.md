# Binary Size Optimization Across Languages

**Date:** 2026-04-02
**Category:** Domain Research -- Compiler/Linker Infrastructure
**Relevance:** Simple compiler binary size strategy, tool binary factoring

---

## 1. Problem Statement

When a compiler/interpreter binary includes ALL compiler passes, ALL standard library code, and ALL backends, the resulting binary becomes large -- often tens or hundreds of megabytes. This research surveys how major languages handle binary size explosion and what techniques exist to mitigate it.

The specific motivating pattern: a language toolchain binary that statically links an entire compiler pipeline, multiple code-generation backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan), a full standard library, an interpreter, and tool-server infrastructure (MCP, LSP). Even if a particular invocation only uses 5% of this code, 100% ships in the binary.

---

## 2. Rust

### 2.1 Why Rust Binaries Are Large

**Monomorphization** is the primary driver. Every generic function instantiated with a concrete type produces a separate machine-code copy. A single `Vec<T>` used with 20 types means 20 copies of every `Vec` method. Real-world measurements:

| Crate | Debug binary | Release binary | Stripped release |
|-------|-------------|---------------|-----------------|
| Hello world | ~4.2 MB | ~400 KB | ~300 KB |
| Actix-web hello | ~60 MB | ~12 MB | ~8 MB |
| ripgrep | ~45 MB | ~6.5 MB | ~4.5 MB |
| rustc (stage2) | -- | ~250 MB | ~180 MB |

**libstd static linking**: Rust statically links its standard library by default. The `std` crate alone contributes ~1.5-3 MB of code. This includes:
- Panic/unwind infrastructure (~200-400 KB)
- Formatting machinery (`std::fmt`) -- heavily monomorphized (~300-500 KB)
- HashMap/BTreeMap/Vec implementations
- I/O buffering, path handling, OsString

**Panic infrastructure**: The default `panic=unwind` pulls in libunwind (~150 KB), DWARF unwinding tables, and landing pad code at every function that could panic. Switching to `panic=abort` removes all of this.

**RTTI and type metadata**: Rust does not have traditional RTTI, but it does emit type descriptors for `Any`, `TypeId`, and vtables for trait objects. Each `dyn Trait` usage generates a vtable.

**Debug info**: Even in release mode, Rust includes some debug info by default (`debuginfo=0` is not the default in many configurations). A release binary with `debuginfo=2` can be 3-5x larger than without.

### 2.2 Rust Solutions

| Technique | Size reduction | Build time impact | Notes |
|-----------|---------------|-------------------|-------|
| `strip = true` | 20-50% | None | Removes symbol tables, debug info |
| `panic = "abort"` | 5-15% | Slight improvement | Removes unwind tables, landing pads |
| `opt-level = "z"` | 10-30% vs `opt-level = 3` | Longer | Optimizes for size over speed |
| `lto = true` (full) | 10-25% | 2-5x longer | Cross-crate dead code elimination |
| `lto = "thin"` | 5-15% | 1.5-2x longer | Parallelizable, nearly as good |
| `codegen-units = 1` | 5-10% | 1.5-2x longer | Better inlining/DCE within crate |
| `Cargo.toml` feature gates | Variable | None | Only compile needed features |

**Full optimization Cargo.toml profile:**
```toml
[profile.release]
opt-level = "z"
lto = true
codegen-units = 1
panic = "abort"
strip = true
```

**Real example**: ripgrep with all optimizations goes from ~6.5 MB to ~2.8 MB.

**`cargo-bloat`** identifies which functions/crates contribute most to binary size. Common findings:
- `std::fmt` machinery: 5-15% of many binaries
- `regex` crate: 500 KB-2 MB (DFA tables)
- `serde_json`: 200-500 KB (monomorphized deserializers)
- Duplicated monomorphized generics across crates

**Shared generics** (`-Zshare-generics`, stabilized in nightly): Allows multiple crates to share the same monomorphized instance instead of each crate generating its own copy. Can reduce binary size by 5-15% for generic-heavy code.

### 2.3 Rust Linker-Level Techniques

Rust uses LLVM's linker plugin for LTO. The linker sees LLVM IR from all compilation units and can:
- Eliminate unused functions across crate boundaries
- Merge identical functions (ICF -- Identical Code Folding)
- Inline across crate boundaries
- Remove unused vtables

`lld` (LLVM's linker) supports `--icf=safe` which merges functions with identical machine code. This is particularly effective for monomorphized generics where `Vec<u32>::push` and `Vec<i32>::push` may generate identical code.

---

## 3. Go

### 3.1 Why Go Binaries Are Large

A Go "hello world" is approximately **1.8-2.1 MB** (Go 1.22+, down from ~2.5 MB in Go 1.18). The causes:

**Runtime overhead**: Every Go binary includes:
- Goroutine scheduler (~150 KB)
- Garbage collector (~200 KB)
- Stack management (growable stacks, stack copying)
- Channel implementation
- Runtime type information for interfaces
- Reflection support (`reflect` package data)

**Static linking by default**: Go statically links everything, including the runtime. There is no shared `libgo.so` that binaries link against (unlike Java's JVM or Python's libpython).

**Interface dispatch tables**: Go's interface system requires runtime type descriptors (itabs) for every (concrete type, interface) pair that exists in the program. The linker generates these tables. Each itab is small (~40 bytes), but large programs with many types and interfaces accumulate thousands.

**String and type descriptors**: Go embeds full type names as strings for reflection, stack traces, and interface satisfaction checking. The `reflect` package prevents the linker from removing type information even if reflection is not explicitly used, because any `interface{}` value might be reflected upon.

### 3.2 Go's Dead Code Elimination

Go's linker (`cmd/link`) performs dead code elimination at the symbol level:

1. **Reachability analysis**: Starting from `main.main` and `runtime.*`, the linker traces all reachable symbols. Unreachable functions are not included in the final binary.
2. **Interface method pruning** (Go 1.22+): The linker can now identify when an interface method is never called and eliminate the corresponding itab entries.
3. **`//go:linkname` complications**: This directive allows accessing unexported symbols, which prevents the linker from safely removing them.

**Limitations**:
- Go does not do function-level section splitting by default (each package is one object file)
- No LTO in the traditional sense (Go compiles and links in one toolchain)
- The `reflect` package can reference any type, making it hard to prove types are unused
- `init()` functions always execute, pulling in their transitive dependencies

### 3.3 Go Size Reduction

| Technique | Size reduction | Notes |
|-----------|---------------|-------|
| `go build -ldflags="-s -w"` | 20-30% | Strip symbol table and DWARF |
| `-trimpath` | 1-2% | Remove filesystem paths from binary |
| UPX compression | 50-70% | But slower startup, breaks on some platforms |
| `GOFLAGS=-buildmode=pie` | Varies | Position-independent, may reduce or increase |
| Avoiding `reflect` | 5-15% | Less type metadata retained |
| Avoiding `fmt` | 3-5% | `fmt` pulls in reflection |
| TinyGo | 50-90% | Alternative compiler for embedded, no GC |

**TinyGo** deserves special mention: it produces binaries 10-100x smaller than standard Go by using LLVM, eliminating the Go runtime, and replacing the GC with a simpler implementation. A TinyGo hello world is ~15 KB. However, it does not support all Go features (no full reflection, limited goroutine support).

---

## 4. C/C++

### 4.1 Section-Based Garbage Collection

The C/C++ ecosystem relies on a cooperation between compiler and linker:

**Compiler side** (`-ffunction-sections -fdata-sections`):
- Without these flags, all functions in a translation unit go into one `.text` section and all data into one `.data`/`.rodata` section. The linker can only include or exclude entire sections.
- With these flags, each function gets its own `.text.function_name` section, and each global variable gets its own `.data.variable_name` or `.rodata.variable_name` section.
- Overhead: slightly larger object files (more section headers), slightly slower linking.

**Linker side** (`--gc-sections` / `-Wl,--gc-sections`):
- The linker performs reachability analysis starting from entry points (`_start`, `main`) and section group roots.
- Any section not reachable is discarded.
- This is the primary mechanism for dead code elimination in C/C++.

**Effectiveness example** (real measurements from a medium-sized C project):

| Configuration | Binary size |
|--------------|------------|
| Default (`-O2`) | 4.8 MB |
| `-O2 -ffunction-sections -fdata-sections -Wl,--gc-sections` | 3.1 MB (35% reduction) |
| Above + `-Os` | 2.4 MB (50% reduction) |
| Above + LTO | 1.9 MB (60% reduction) |
| Above + strip | 1.2 MB (75% reduction) |

### 4.2 Link-Time Optimization (LTO)

**Full (monolithic) LTO**:
- The compiler emits LLVM bitcode (or GCC's GIMPLE IR) into object files instead of machine code
- At link time, all bitcode is merged into a single module
- The optimizer runs on the entire program as one unit
- Enables: cross-TU inlining, global DCE, global constant propagation, cross-TU devirtualization
- Drawback: link time scales quadratically, requires enormous RAM for large projects (LLVM/Clang itself needs 30+ GB RAM to LTO link)
- Size reduction: typically 10-30%

**Thin LTO** (LLVM-specific, introduced in LLVM 4.0):
- Each TU is compiled to bitcode independently
- A thin "summary" of each module is generated (function signatures, call graph edges, type info)
- The linker examines summaries to make import/export decisions
- Each module is then optimized in parallel, importing only specific functions from other modules
- Drawback: slightly less optimization opportunity than full LTO
- Advantage: parallelizes well, uses far less RAM
- Size reduction: typically 8-25% (vs 10-30% for full LTO)

**LTO with GCC** (`-flto`):
- GCC uses GIMPLE (its intermediate representation) streamed into ELF sections
- `lto1` merges all GIMPLE and runs whole-program optimization
- GCC supports LTO partitioning for parallel optimization (similar concept to Thin LTO)
- GCC's LTO is generally considered less mature than LLVM's for very large projects

### 4.3 C++ Specific Bloat Sources

**Templates**: C++ templates are instantiated per-TU. Without LTO, duplicate instantiations exist across TUs. The linker uses COMDAT groups to deduplicate:
- `std::vector<int>::push_back` instantiated in 50 TUs -> linker keeps one copy
- COMDAT folding handles exact duplicates but not near-duplicates

**Exceptions**: C++ exception handling adds:
- `.eh_frame` section: DWARF unwinding information (~10-20% of text size)
- `.gcc_except_table`: Landing pad tables
- Exception type info (`typeinfo` objects)
- `-fno-exceptions` can save 10-20% in exception-heavy code

**RTTI**: `dynamic_cast` and `typeid` require type information objects:
- Each polymorphic class gets a `typeinfo` object and `typeinfo name` string
- `-fno-rtti` removes these (saves ~1-5%)
- But breaks `dynamic_cast`, `typeid`, and `catch` by derived type

**Virtual dispatch tables (vtables)**:
- Each polymorphic class generates a vtable
- Vtables are typically emitted in the TU containing the first non-inline virtual method
- The linker cannot remove vtables for classes that might be constructed (conservatively kept)
- Devirtualization (LTO) can eliminate vtable entries when the concrete type is known

### 4.4 Linker Implementations Compared

| Feature | GNU ld | gold | lld | mold |
|---------|--------|------|-----|------|
| `--gc-sections` | Yes | Yes | Yes | Yes |
| `--icf=safe` | No | Yes | Yes | Yes |
| `--icf=all` | No | Yes | Yes | Yes |
| Full LTO | Yes (plugin) | Yes (plugin) | Native | No |
| Thin LTO | No | Yes (plugin) | Native | No |
| Speed (relative) | 1x | 2-4x | 3-5x | 5-15x |

**Identical Code Folding (ICF)**:
- `--icf=safe`: Merge functions with identical code that do not have their address taken
- `--icf=all`: Merge all identical functions (may break pointer comparison)
- Particularly effective for C++ templates and Rust monomorphization
- Typical savings: 5-15% on C++ binaries

**mold** (by Rui Ueyama, 2021+):
- Fastest linker available, designed for development iteration
- Does NOT support LTO (by design -- LTO dominates link time anyway)
- Supports ICF, gc-sections, and most common linker features
- 5-15x faster than GNU ld for large projects

---

## 5. Zig

### 5.1 How Zig Achieves Small Binaries

Zig is notable for producing remarkably small binaries, often smaller than equivalent C:

| Program | C (gcc -Os) | Zig (ReleaseSafe) | Zig (ReleaseSmall) |
|---------|------------|-------------------|-------------------|
| Hello world (static) | ~700 KB | ~6 KB | ~3 KB |
| Hello world (dynamic) | ~16 KB | ~6 KB | ~3 KB |
| HTTP server | ~2 MB | ~800 KB | ~400 KB |

**Key strategies**:

1. **No runtime by default**: Zig has no garbage collector, no goroutine scheduler, no heavyweight runtime. The "runtime" is ~2 KB of startup code and optional safety checks.

2. **Lazy compilation**: Zig only compiles code that is actually reachable. This is done at the semantic analysis level, not the linker level. If you `@import` a module with 1000 functions but only call 3, only those 3 (and their transitive dependencies) are compiled at all. The compiler never generates code for unused functions.

3. **Comptime evaluation**: Zig's `comptime` aggressively evaluates code at compile time. Complex initialization, lookup tables, and configuration are resolved before any code is generated. This means less runtime code.

4. **No hidden control flow**: No exceptions (no unwind tables), no hidden allocations, no implicit function calls. What you write is what executes.

5. **LLVM backend with full optimization**: Zig uses LLVM and can apply full LTO, ICF, and gc-sections. The `ReleaseSmall` mode uses `-Os` equivalent optimization.

6. **No format string machinery by default**: Unlike C's `printf` or Rust's `std::fmt`, Zig's `std.debug.print` is comptime-resolved. The format string is parsed at compile time, generating only the specific printing code needed.

7. **Optional standard library**: Zig's standard library is pay-for-what-you-use. You can build freestanding binaries that use none of it.

### 5.2 Zig's Dead Code Elimination

Zig's approach is fundamentally different from C/C++/Rust:

- **Semantic-level DCE**: The compiler itself tracks which declarations are referenced. Unreferenced declarations are never analyzed, type-checked, or compiled. This is more aggressive than linker-level GC because it eliminates code before it even reaches the backend.
- **No separate compilation model**: Zig compiles the entire program as one compilation unit (similar to LTO by default). This gives the compiler full visibility for optimization.
- **Generic instantiation is lazy**: Like Rust, Zig monomorphizes generics. But because of lazy compilation, only actually-used instantiations are generated.

---

## 6. Swift

### 6.1 Binary Size with Generics/Protocols

Swift uses a hybrid approach to generics:

**Witness tables** (protocol oriented):
- Each (type, protocol) conformance generates a Protocol Witness Table (PWT)
- PWTs contain function pointers to the concrete implementations
- A Value Witness Table (VWT) describes size, alignment, copy/move/destroy for each type
- These tables are per-type, not per-instantiation, so they scale linearly with the number of conformances

**Specialization** (monomorphization, optional):
- Swift's SIL (Swift Intermediate Language) optimizer can specialize generic functions for concrete types
- This is controlled by `@_specialize` attribute and optimization level
- At `-O` (optimize for speed), the compiler aggressively specializes
- At `-Osize`, the compiler prefers unspecialized (witness-table-based) generics
- Unspecialized generics use indirect dispatch through witness tables, producing smaller but slower code

**Comparison of approaches**:
```
Rust: Always monomorphize (one machine code copy per type parameter combination)
Swift -O: Monomorphize hot paths, use witness tables for cold paths
Swift -Osize: Prefer witness tables, minimize specialization
Go: No generics monomorphization (until Go 1.18+, and even then limited)
Zig: Lazy monomorphization (only compile what's used)
```

### 6.2 Swift-Specific Size Concerns

**Objective-C metadata**: On Apple platforms, Swift classes that interact with Objective-C carry significant metadata:
- Class metadata structures
- Method dispatch tables (objc_method_description)
- Property reflection metadata
- Protocol conformance records

**String metadata**: Swift stores rich type metadata as strings for reflection, debugging, and dynamic casting. This includes mangled type names.

**ABI stability** (Swift 5.0+): On Apple platforms, the Swift runtime ships with the OS. This means Swift binaries on iOS 13+ / macOS 10.15+ do not need to embed the Swift runtime (~5-10 MB saving). On Linux, the runtime must still be bundled or dynamically linked.

### 6.3 Swift Size Reduction

| Technique | Savings | Notes |
|-----------|---------|-------|
| `-Osize` | 10-30% vs `-O` | Reduces specialization |
| Strip (`strip -x`) | 20-40% | Remove symbols |
| `-whole-module-optimization` | 5-15% | Cross-file optimization, better DCE |
| Dead code stripping (`-dead_strip`) | 5-20% | Apple linker's gc-sections equivalent |
| `@_implementationOnly import` | Variable | Prevent ABI metadata export |
| Bitcode (deprecated in Xcode 14) | N/A | Was used for App Store re-optimization |

---

## 7. Key Techniques Deep Dive

### 7.1 Link-Time Optimization (LTO): Thin vs Full

```
                    Full LTO                          Thin LTO
Compilation    Emit IR per TU                    Emit IR + summary per TU
Merging        Merge ALL IR into one module       Read summaries only
Optimization   One big optimization pass          Parallel optimization per module
                                                  (importing cross-module functions)
RAM usage      O(program size)                    O(module size + imports)
Parallelism    None (single module)               Full (per module)
Link time      Very long for large programs       2-5x faster than full LTO
Quality        Best possible optimization         ~95% of full LTO quality
Size savings   10-30%                             8-25%
```

**When full LTO matters**: Programs under ~1M lines of code where the extra 5% optimization is worth the build time. Beyond that, Thin LTO is almost always preferred.

**Real measurements (Chromium, ~35M lines)**:
- Full LTO: impractical (requires 64+ GB RAM, hours of link time)
- Thin LTO: +15% link time, -8% binary size, -5% runtime improvement
- Chromium uses Thin LTO in production builds

### 7.2 Dead Code Elimination / Tree Shaking

**Levels of DCE**:

1. **Compiler-level DCE** (within a TU/module):
   - Remove unreachable basic blocks
   - Remove unused local variables and functions with internal linkage
   - Constant fold and eliminate dead branches
   - Available in all compilers at `-O1` and above

2. **Linker-level DCE** (`--gc-sections`):
   - Remove unreachable sections (functions, data) across the entire program
   - Requires `-ffunction-sections -fdata-sections` for fine granularity
   - The linker builds a reference graph from entry points and discards unreferenced sections
   - Cannot remove partially-used sections

3. **LTO-level DCE**:
   - The optimizer sees the entire program as one unit
   - Can eliminate functions proven unreachable through interprocedural analysis
   - Can devirtualize calls and then eliminate now-unreachable virtual methods
   - Can propagate constants across TU boundaries and eliminate dead branches

4. **Semantic-level DCE** (Zig, some module systems):
   - The compiler itself never compiles unreferenced code
   - Most aggressive form, but requires whole-program compilation

**JavaScript tree shaking comparison**:
- Webpack/Rollup/esbuild perform tree shaking on ES modules
- Based on static analysis of `import`/`export` statements
- Cannot tree-shake CommonJS `require()` (dynamic)
- Side effects prevent elimination (`"sideEffects": false` in package.json)
- This is analogous to linker DCE but at the module/export level

### 7.3 Symbol Visibility Control

**ELF visibility attributes**:
```c
__attribute__((visibility("default")))  // Exported (visible to other shared libs)
__attribute__((visibility("hidden")))   // Internal (not visible outside the shared lib)
```

- `-fvisibility=hidden` makes all symbols hidden by default
- Only explicitly exported symbols are visible
- Hidden symbols can be optimized more aggressively (no need to preserve calling convention for external callers)
- Reduces symbol table size and enables better optimization
- Critical for shared libraries: a shared library with 10,000 exported symbols has a much larger `.dynsym` and slower dynamic linking than one with 100

**Rust**: All symbols are effectively hidden except `#[no_mangle]` and `pub extern` functions. Rust's symbol mangling prevents accidental visibility.

**Go**: All symbols are internal (Go does not produce shared libraries in the traditional sense, though `-buildmode=c-shared` exists).

### 7.4 Dynamic vs Static Linking

| Aspect | Static | Dynamic |
|--------|--------|---------|
| Binary size | Larger (includes all library code) | Smaller (only PLT stubs) |
| Disk usage (N binaries using same lib) | N copies of lib code | 1 shared copy |
| RAM usage | N copies in memory | 1 copy shared via mmap |
| Startup time | Faster (no dynamic linker) | Slower (symbol resolution) |
| Deployment | Self-contained | Requires library installation |
| DCE opportunity | Full (linker removes unused) | None (entire .so loaded) |
| Security updates | Requires rebuild | Replace .so, restart |

**The paradox**: Static linking produces larger individual binaries but allows better dead code elimination. Dynamic linking produces smaller individual binaries but loads entire libraries even if only one function is used.

**Partial static linking**: Some ecosystems support hybrid approaches:
- Linux: `glibc` dynamically linked, everything else static
- Rust: Can use `+crt-static` to statically link the C runtime while dynamically linking system libraries
- Go: CGO_ENABLED=0 forces fully static; CGO_ENABLED=1 dynamically links libc

### 7.5 Monomorphization Bloat Mitigation

**Outline generics** (Swift, some proposals for Rust):
- Instead of generating N copies for N type parameters, generate one "outlined" function that takes type metadata as a parameter
- The outlined function uses indirect dispatch (through vtables/witness tables) for type-specific operations
- Tradeoff: smaller code but slower execution (indirect calls, no inlining)

**Polymorphization** (Rust RFC 2781, partially implemented):
- Detect when a generic function does not actually use its type parameter in a type-dependent way
- Example: `fn len<T>(v: &Vec<T>) -> usize { v.len }` -- the generated code is identical for all T
- Share a single implementation across all instantiations
- Current status: has been partially implemented in rustc but disabled by default due to ICEs

**Identical Code Folding (ICF)**:
- The linker detects functions with identical machine code and merges them
- Particularly effective after monomorphization
- `--icf=safe` is safe for most programs
- `--icf=all` merges even functions whose address is taken (can break `fn_ptr_a == fn_ptr_b`)
- Typical savings: 5-15% on heavily generic code

**Manual mitigation patterns**:
```rust
// BLOATING: Each T generates a full copy
fn process<T: Serialize>(items: Vec<T>) {
    for item in items {
        let json = serde_json::to_string(&item).unwrap();
        // ... 200 lines of code processing json ...
    }
}

// BETTER: Only the thin wrapper is monomorphized
fn process<T: Serialize>(items: Vec<T>) {
    for item in items {
        let json = serde_json::to_string(&item).unwrap();
        process_json(json); // Non-generic inner function
    }
}

fn process_json(json: String) {
    // ... 200 lines of code processing json ...
}
```

### 7.6 Section-Based GC in Linkers

**How it works in detail**:

```
Compilation (-ffunction-sections -fdata-sections):
  foo.c contains: fn_a(), fn_b(), fn_c(), global_x, global_y
  Produces sections: .text.fn_a, .text.fn_b, .text.fn_c, .data.global_x, .rodata.global_y

Linking (--gc-sections):
  1. Mark entry points as live: main, _start, .init_array entries, .ctors
  2. For each live section, examine relocations:
     - .text.main references .text.fn_a -> mark .text.fn_a live
     - .text.fn_a references .rodata.global_y -> mark .rodata.global_y live
  3. .text.fn_b, .text.fn_c, .data.global_x are unreachable -> discard

  Without -ffunction-sections:
  foo.c produces one .text section containing fn_a, fn_b, fn_c
  Linker must keep all three even if only fn_a is used
```

**Limitations**:
- Cannot split within a function (entire function is kept or discarded)
- Relocations are conservative: if a section MENTIONS another section, it's marked live
- Global constructors (`.init_array`, `.ctors`) are always marked live
- Exception handling tables reference their associated code sections, creating additional live roots

### 7.7 Symbol Stripping

**What can be stripped**:
- `.symtab` (static symbol table): Function/variable names for debugging
- `.strtab` (string table): Symbol name strings
- `.debug_*` sections: DWARF debugging information
- `.comment` section: Compiler version strings

**What cannot be stripped**:
- `.dynsym` (dynamic symbol table): Required for dynamic linking
- `.dynstr` (dynamic string table): Required for dynamic linking
- `.text` (code): Obviously required
- `.rodata` (read-only data): String literals, constants
- `.eh_frame` (exception handling): Required for stack unwinding (C++ exceptions, Rust panics)

**Strip levels**:
```bash
strip --strip-debug binary    # Remove debug info only
strip --strip-unneeded binary # Remove debug + unnecessary symbols
strip --strip-all binary      # Remove everything possible (may break dlopen)
```

**Typical savings**: 20-50% of binary size is debug info and symbols.

### 7.8 Compression

**UPX (Ultimate Packer for eXecutables)**:
- Compresses the executable and prepends a decompression stub (~50 KB)
- At runtime, the stub decompresses the binary into memory and jumps to it
- Compression ratio: 50-70% size reduction
- Drawbacks:
  - Slower startup (decompression time: 10-100ms depending on binary size)
  - Higher RSS (entire binary must be in memory, cannot page-fault in individual pages)
  - Some antivirus software flags UPX-packed binaries
  - Breaks code signing
  - Breaks memory-mapped I/O patterns
  - Cannot share pages between identical processes
- Use case: Distribution of CLI tools where download size matters more than startup time

**Alternative: zstd/lz4 self-extracting**:
- Custom self-extracting archives that decompress to /tmp and exec
- More flexible than UPX
- Can cache decompressed binary for subsequent runs

---

## 8. The Monolithic Compiler Binary Problem

### 8.1 How Existing Ecosystems Handle It

**GCC: Separate binaries per tool**
```
gcc (driver) -> cc1 (C compiler) -> as (assembler) -> collect2 -> ld (linker)
              -> cc1plus (C++ compiler)
              -> f951 (Fortran compiler)
              -> lto1 (LTO optimizer)
```
- Each tool is a separate binary
- `cc1` (the actual C compiler) is ~30 MB; `cc1plus` is ~35 MB
- The `gcc` driver is tiny (~1 MB) and orchestrates subprocess calls
- Advantage: Only the needed tool loads into memory
- Disadvantage: Process startup overhead, IPC overhead for LTO

**Clang/LLVM: One big binary, multiple entry points**
```
clang (~100 MB) handles: C, C++, Objective-C, CUDA, OpenCL
  Internally: Frontend (Clang) -> LLVM IR -> LLVM optimizer -> LLVM codegen
  clang++ is a symlink to clang (argv[0] detection)
  clang-cl is a symlink to clang (MSVC-compatible driver)
```
- Clang chose the monolithic approach for faster LTO and tighter integration
- `clang` binary includes all frontends and all backends
- LLVM tools (`llc`, `opt`, `llvm-ar`, etc.) share `libLLVM.so` (~80 MB) when built as shared library
- Build option: `LLVM_LINK_LLVM_DYLIB=ON` builds one `libLLVM.so` shared by all tools
- This reduces total disk usage but each tool still loads the full library

**LLVM's multicall binary approach** (`llvm-driver`):
- Since LLVM 15, there's a `llvm` multicall binary (like BusyBox)
- `llvm ar`, `llvm nm`, `llvm objdump` all invoke the same binary
- Saves disk space by sharing code
- But does NOT save memory or reduce what's linked in

**Rust toolchain: rustc + separate tools**
```
rustc (~250 MB) - compiler
cargo (~25 MB) - build system (separate binary)
rustfmt (~10 MB) - formatter (separate binary)  
clippy-driver (~250 MB) - linter (links against same libraries as rustc)
rust-analyzer (~100 MB) - LSP server (separate binary)
```
- `rustc` is monolithic but only includes the compiler
- Tools are separate binaries
- `clippy` is essentially a modified `rustc` and is similarly large
- `rust-analyzer` is a separate implementation, not based on `rustc`

**Node.js: Small entry point, dynamic module loading**
```
node (~80 MB) - V8 engine + core modules
  Individual tools are just scripts:
  npx -> node npx.js
  npm -> node npm.js
  tsc -> node tsc.js
```
- The engine is large but tools are tiny scripts
- Module loading is dynamic (require/import at runtime)
- Unused modules never load into memory
- Drawback: V8 itself is large regardless of what you run

### 8.2 Patterns for the Simple Compiler

Given the Simple compiler's architecture (all passes, all backends, interpreter, MCP server, LSP server in one binary), several strategies apply:

**Strategy 1: Feature Flags at Compile Time**
```
simple build --features=core,c-backend           # Minimal: only C backend
simple build --features=core,llvm-backend         # LLVM only
simple build --features=all                       # Everything
simple build --features=core,mcp-server           # MCP tool server
```
- Compile-time feature selection excludes unused backends entirely
- Requires modular architecture with clear dependency boundaries
- Most effective strategy: prevents code from ever being compiled

**Strategy 2: Separate Tool Binaries**
```
bin/simple              # Compiler/interpreter (core)
bin/simple_mcp_server   # MCP server (links against compiler lib)
bin/simple_lsp_server   # LSP server
bin/simple_fmt          # Formatter
```
- Already partially implemented in the Simple project
- Each tool only links the code it needs
- Shared library (`.so`/`.dylib`/`.dll`) can reduce disk duplication

**Strategy 3: Plugin Architecture**
```
bin/simple                          # Core compiler + interpreter
lib/simple_backend_llvm.so          # LLVM backend (loaded on demand)
lib/simple_backend_c.so             # C backend
lib/simple_backend_cranelift.so     # Cranelift backend
lib/simple_backend_cuda.so          # CUDA backend
```
- Dynamic loading of backends via `dlopen`/`LoadLibrary`
- Core binary stays small
- Backends loaded only when requested
- Drawback: deployment complexity, dynamic linking issues

**Strategy 4: Multicall Binary (BusyBox Pattern)**
```
bin/simple                          # One binary
bin/simple_mcp -> bin/simple        # Symlink
bin/simple_lsp -> bin/simple        # Symlink
bin/simple_fmt -> bin/simple        # Symlink
```
- Single binary, behavior determined by `argv[0]`
- Saves disk space when tools share most code
- Does NOT save memory (entire binary still loaded)
- Used by: BusyBox, LLVM, Clang, toybox

**Strategy 5: Lazy Module Loading (Internal)**
- The compiler binary includes all code but loads internal modules lazily
- Backend initialization deferred until actually needed
- This does not reduce binary size but reduces memory usage
- Effective when combined with section-based GC (unused but loaded code stays on cold pages)

### 8.3 Recommended Approach for Simple

Based on the research, a layered strategy is most effective:

1. **Immediate wins** (no architecture changes needed):
   - Enable LTO (Thin LTO for dev builds, Full LTO for releases)
   - Enable `--gc-sections` with `-ffunction-sections -fdata-sections`
   - Strip release binaries
   - Use `panic=abort` equivalent
   - Enable ICF (`--icf=safe`)
   - Expected savings: 40-60% of current binary size

2. **Medium-term** (requires some refactoring):
   - Feature-flag backends so unused ones are not compiled
   - Separate MCP/LSP servers into their own binaries (already partially done)
   - Non-generic inner functions pattern for hot monomorphized code
   - Expected additional savings: 20-40%

3. **Long-term** (architecture decision):
   - Plugin architecture for backends (`dlopen`-based)
   - Shared library for compiler core
   - Multicall binary for related tools
   - Expected additional savings: varies by deployment scenario

---

## 9. What Linkers Cannot Remove

Understanding what survives even aggressive optimization:

### 9.1 Always Retained

| Category | Why it survives | Mitigation |
|----------|----------------|------------|
| Virtual dispatch tables (vtables) | Conservative analysis cannot prove a type is never constructed | LTO devirtualization, `final` keyword |
| Type metadata (RTTI) | Could be used by any `dynamic_cast`/`typeid` | `-fno-rtti` (C++), avoid reflection |
| Global constructors (`.init_array`) | Always executed before `main` | Minimize static initialization |
| Exception handling tables (`.eh_frame`) | Stack unwinding needs frame info for every function | `-fno-exceptions`, `panic=abort` |
| Thread-local storage init | TLS variables require init/cleanup | Minimize TLS usage |
| Debug info (if not stripped) | Linked to code sections | `strip` |
| PLT/GOT entries (dynamic linking) | Required for symbol resolution | Static linking |
| String literals referenced by live code | Transitively live | Shorter strings, string interning |
| Alignment padding | Required by ABI | `-falign-functions=1` (can hurt performance) |

### 9.2 Hard-to-Remove Patterns

**Trait objects / virtual dispatch**:
```rust
// The compiler cannot prove which concrete types might be behind `dyn Animal`
fn process(animal: &dyn Animal) { animal.speak(); }
// All types implementing Animal must keep their vtables and speak() implementations
```

**Reflection/introspection**:
```go
// Any type might be reflected upon
func process(v interface{}) {
    t := reflect.TypeOf(v) // Prevents linker from removing type info
}
```

**Plugin/extension points**:
```c
// Registration pattern prevents DCE
static void __attribute__((constructor)) register_plugin() {
    register_backend("llvm", &llvm_backend_vtable);
}
// The constructor always runs, making the backend always "live"
```

**Conditional compilation is the only reliable solution** for these patterns. If a backend is never compiled, its vtables, constructors, and metadata cannot exist.

---

## 10. Quantitative Summary

### 10.1 Technique Effectiveness Matrix

| Technique | Typical savings | Build cost | Runtime cost | Complexity |
|-----------|----------------|-----------|-------------|------------|
| Strip symbols | 20-50% | None | None | Trivial |
| `-Os`/`opt-level=z` | 10-30% | Moderate | 5-15% slower | Trivial |
| `--gc-sections` | 10-35% | Minimal | None | Low |
| Full LTO | 10-30% | 2-5x slower | Often faster | Low |
| Thin LTO | 8-25% | 1.5-2x slower | Often faster | Low |
| ICF (`--icf=safe`) | 5-15% | Minimal | None | Low |
| `panic=abort` / `-fno-exceptions` | 5-20% | None | None | Low |
| `-fno-rtti` (C++) | 1-5% | None | Breaks dynamic_cast | Low |
| Feature flags | 20-80% | None | None | Medium |
| Separate binaries | 30-70% per binary | Moderate | None | Medium |
| Plugin architecture | 50-90% of core | Moderate | dlopen overhead | High |
| UPX compression | 50-70% on disk | 1-2s | 10-100ms startup | Low |

### 10.2 Binary Size Hall of Fame

| Binary | Language | Size (stripped) | What it includes |
|--------|----------|----------------|-----------------|
| BusyBox | C | ~1 MB | 300+ Unix utilities |
| toybox | C | ~800 KB | 200+ Unix utilities |
| TinyGo hello | Go/TinyGo | ~15 KB | Minimal runtime |
| Zig hello (static) | Zig | ~3 KB | No runtime |
| Go hello | Go | ~1.5 MB | Full runtime + GC |
| Rust hello | Rust | ~300 KB | Stripped, panic=abort |
| ripgrep | Rust | ~2.8 MB | Full-featured grep |
| Node.js | C++ | ~80 MB | V8 + core modules |
| rustc | Rust | ~180 MB | Full compiler |
| clang | C++ | ~100 MB | All frontends + LLVM |
| GCC cc1 | C | ~30 MB | C compiler only |

---

## 11. Recommendations for Simple

### 11.1 Binary Size Budget

For a language compiler/toolchain, reasonable targets:

| Binary | Target | Notes |
|--------|--------|-------|
| `simple` (compiler+interp) | 15-30 MB | Core functionality only |
| `simple_mcp_server` | 5-10 MB | Compiler lib + MCP protocol |
| `simple_lsp_server` | 5-10 MB | Compiler lib + LSP protocol |
| Total toolchain (all binaries) | 30-50 MB | With shared library: less |

### 11.2 Checklist for Release Builds

- [ ] Enable Thin LTO (or Full LTO if build time allows)
- [ ] Use `-ffunction-sections -fdata-sections` for C/C++ components
- [ ] Pass `--gc-sections` to the linker
- [ ] Pass `--icf=safe` to lld/gold
- [ ] Strip the release binary (`strip --strip-all` or equivalent)
- [ ] Use size-optimized profile for release (`-Os` / `opt-level=z`)
- [ ] Disable panic unwinding in favor of abort
- [ ] Feature-gate backends not needed for a particular build
- [ ] Measure binary size in CI and track regressions

### 11.3 Architecture Principles

1. **Separate concerns into libraries**: Compiler core, backends, tool servers should be separate link-time units. Even if built into one binary, they should be structured so the linker can GC unused parts.

2. **Avoid global constructors for registration**: Use explicit initialization instead of constructor-based auto-registration. This allows the linker to eliminate unneeded backends.

3. **Minimize monomorphization surface**: Keep generic functions thin; delegate to non-generic implementations for the bulk of logic.

4. **Prefer compile-time feature selection over runtime**: Dead code that is never compiled is guaranteed to be zero-cost. Runtime checks still require the code to exist in the binary.

5. **Profile binary size regularly**: Tools like `bloaty` (Google's binary size profiler), `cargo-bloat`, and `llvm-nm --size-sort` reveal what's consuming space.

---

## 12. References

- Rust min-sized-rust guide: https://github.com/nickel-org/nickel.rs/wiki/Reducing-binary-size
- Google Bloaty McBloatface: https://github.com/google/bloaty
- LLVM Thin LTO design: https://clang.llvm.org/docs/ThinLTO.html
- Zig's approach to binary size: https://ziglang.org/documentation/
- Go binary size tracking: https://github.com/nickel-org/nickel.rs/wiki
- mold linker design: https://github.com/rui314/mold
- "Shrinking Rust binaries" by John Googling (2024)
- LLVM ICF documentation: https://lld.llvm.org/
- Swift binary size optimization: https://developer.apple.com/documentation/xcode/reducing-your-app-s-size
