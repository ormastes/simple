# T32 MCP Native Binary Size Explosion — Root Cause Analysis

**Date:** 2026-04-02  
**Binary:** `bin/release/t32_mcp_native` — **177 MB** (18 `.spl` source files → 177 MB binary)

---

## 1. Measured Binary Sizes

| Binary | Size | Source Files | Ratio |
|--------|------|-------------|-------|
| `t32_mcp_native` | **177 MB** | 18 `.spl` | 9.8 MB/file |
| `libsimple_runtime.a` | **133 MB** | (static lib) | — |
| `simple_native` | **86 MB** | full compiler | — |
| `t32_lsp_mcp_tool_runner` | **27 MB** | — | — |
| `simple.bak.pre_new` | **17 MB** | older release | — |

**The T32 MCP server (18 files) produces a binary 2× larger than the entire Simple compiler (4,527 files).** This is the core anomaly.

---

## 2. Root Causes (Ordered by Impact)

### 2.1 — `--whole-archive` Forces ALL Symbols Into Binary (CRITICAL)

**File:** `src/compiler_rust/compiler/src/pipeline/native_project.rs:1335-1388`

```rust
// Line 1335: "Link the archive. Use -force_load/--whole-archive to include all symbols"
// Line 1345: cmd.arg("-Wl,--whole-archive")
// Line 1359: cmd.arg("-Wl,--whole-archive")  
// Line 1373: "Use --whole-archive to force linking ALL runtime members (not just referenced ones)"
// Line 1386: cmd.arg("-Wl,--whole-archive")
```

`--whole-archive` **defeats the linker's dead code elimination entirely**. Every symbol in `libsimple_runtime.a` (133 MB) is forcibly included, regardless of whether the T32 MCP server uses it. The linker's `--gc-sections` flag (line 584, 798 in `linker_wrapper.spl`) becomes useless because `--whole-archive` already forced every section into the binary.

**Why it exists:** Runtime symbols are referenced indirectly via interpreter dispatch tables, vtables, and string-based symbol lookup. The linker can't see these dynamic references, so `--whole-archive` was added to prevent "undefined symbol" errors at runtime.

**Impact:** ~133 MB of the 177 MB binary comes from the runtime archive alone.

### 2.2 — Whole-Program Source Loading (CRITICAL)

**File:** `src/compiler/80.driver/driver.spl:368-395`

```simple
var has_project_source = false
# ...
if input_path.starts_with("src/"):
    has_project_source = true
# ...
if has_project_source:
    val paths = ["src/app", "src/lib", "src/compiler", "src/runtime"]
    val bulk_loaded = _driver_collect_sources_via_find(paths)
```

When any input file starts with `src/`, the driver **loads ALL 4,527 `.spl` files** from `src/app`, `src/lib`, `src/compiler`, and `src/runtime`. The T32 MCP tools live under `examples/`, so they may avoid this trigger — but any transitive dependency that pulls in an `src/` module triggers the whole-program load.

Even if the T32 MCP build avoids this path, the **runtime archive** (`libsimple_runtime.a`) was compiled from the whole program, so it carries all compiled code regardless.

### 2.3 — `--gc-sections` NOT Passed on Linux in Rust Bootstrap Path (CRITICAL)

**File:** `src/compiler_rust/compiler/src/pipeline/native_project.rs:1450-1463`

On Linux, the primary link path does **NOT** pass `--gc-sections` at all — only `-Wl,-s` for stripping:
```rust
if self.config.strip {
    cmd.arg("-Wl,-s");   // strip only, NO --gc-sections on Linux!
}
// Only MinGW gets --gc-sections:
// cmd.arg("-Wl,--gc-sections").arg("-Wl,-s");
```

The Simple-language linker wrapper (`linker_wrapper.spl:583-584`) does pass `--gc-sections`, but this is a **different code path** from the Rust bootstrap's native-build. The `LinkerBuilder` API (`builder.rs:321`) also has `--gc-sections` but is **not used** by `native_project.rs` — it uses raw `std::process::Command` instead.

### 2.4 — `--entry-closure` Exists But Is Not Default

**File:** `src/compiler_rust/compiler/src/pipeline/native_project.rs:681-690`

An `--entry-closure` flag exists that enables reachability-based discovery from the entry point's import graph. **But it is not the default.** Without it, `discover_files_full_scan()` collects every `.spl` file from all source directories (3,585+ files). Even with `--entry-closure`, the analysis walks `use` statements but does not do function-level DCE.

### 2.5 — Missing `-ffunction-sections -fdata-sections` on Normal Builds

**Baremetal builds have it:** `src/compiler/80.driver/build/baremetal.spl:222-223`
```simple
args.push("-fdata-sections")
args.push("-ffunction-sections")
```

**Normal native builds DO NOT.** The Cranelift backend also does not emit per-function sections — all functions from a single `.spl` file end up in a single `.text` section. Without per-function sections, `--gc-sections` can only discard at file granularity, not function granularity.

### 2.6 — No LTO in Native Build Pipeline

The Rust bootstrap has LTO profiles (`release-opt: lto = "fat"`), but **the native-build pipeline does not pass `-flto`** to clang/gcc. LTO exists only in:
- The self-hosted compiler's FFI build orchestrator (`orchestrator.spl:148-150`) with `--lto` flag
- Cargo.toml for generated FFI wrapper crates (`ffi_gen/` with `lto = "thin"`)

### 2.7 — Debug Info Not Stripped

`bin/release/t32_mcp_native` is **not stripped** (`file` reports "not stripped"). The `NativeBuildConfig` defaults to `strip: false`. There is no `--release` optimization level — the Cranelift backend generates unoptimized code.

### 2.8 — Section Size Breakdown

| Binary | `.text` | `.data` | `.bss` | On-disk |
|--------|---------|---------|--------|---------|
| `t32_mcp_native` | **142.4 MB** | **6.9 MB** | 595 KB | 177 MB |
| `simple_native` | 70.7 MB | 1.1 MB | 253 KB | 86 MB |
| `simple_host` | 21.1 MB | 955 KB | 16 KB | 32 MB |

T32 MCP has **2× the .text** and **6× the .data** of the full compiler. The 34 MB gap between sections (149 MB) and on-disk (177 MB) is **debug info**.

### 2.9 — `libsimple_runtime.a` Duplicated 3×

133 MB × 3 copies exist in `bin/`, `bin/release/`, and `bin/release/linux-x86_64/` — **399 MB of disk wasted**.

---

## 3. How Other Languages Solve This

### 3.1 Rust
| Problem | Solution | Effect |
|---------|----------|--------|
| Monomorphization bloat | `opt-level = "z"`, `codegen-units = 1` | 30-50% reduction |
| Runtime inclusion | `panic = "abort"` (removes unwind tables) | 10-20% reduction |
| Dead code | LTO (`lto = "fat"`) + `strip = "symbols"` | 40-70% reduction |
| All symbols linked | **No `--whole-archive` by default** — Rust uses precise symbol resolution | Prevents the core problem |

Rust avoids the `--whole-archive` trap because `rustc` emits precise symbol dependencies at compile time. The linker only pulls in archive members that define symbols actually referenced.

### 3.2 C/C++
The standard approach uses **three cooperating flags**:
1. **Compile:** `-ffunction-sections -fdata-sections` — each function/global gets its own ELF section
2. **Link:** `-Wl,--gc-sections` — linker discards unreferenced sections
3. **Link:** `-Wl,-s` or `strip` — remove symbol table and debug info

This is the **minimum viable dead code elimination** for C/C++. Without step 1, step 2 is almost useless.

Additionally, C/C++ projects use:
- `-flto` (Link-Time Optimization) for cross-TU elimination
- `-fvisibility=hidden` to mark all symbols as internal by default
- Separate libraries (`.so`/`.dylib`) to avoid linking unused code

### 3.3 Go
Go binaries are famously large (10-20 MB for "hello world") due to:
- Statically linked runtime (GC, goroutine scheduler, netpoller)
- Full reflection metadata for all types
- DWARF debug info included by default

Mitigations: `go build -ldflags="-s -w"` (strip DWARF + symbol table), `-trimpath`, `upx` compression.

Go accepted large binaries as a tradeoff for static linking simplicity.

### 3.4 Zig
Zig achieves small binaries through:
- **Lazy compilation** — only compiles functions that are actually called (semantic analysis is demand-driven)
- **No runtime** by default — `@import("std")` is tree-shaken aggressively
- `-OReleaseFast` or `-OReleaseSmall` with automatic dead code elimination
- Zig's linker (`zld`/custom) does fine-grained symbol-level GC

### 3.5 The Modular Approach (GCC/LLVM)
Large compiler projects avoid monolithic binaries entirely:
- **GCC:** Separate binaries — `cc1` (C frontend), `cc1plus` (C++), `as` (assembler), `collect2`/`ld` (linker)
- **LLVM:** Shared library architecture — `libLLVM.so` loaded by `clang`, `opt`, `llc` independently
- **JVM/Node.js:** Dynamic module loading — only load what's imported at runtime

---

## 4. Recommended Fixes (Priority Order)

### Fix 1: Remove `--whole-archive` + Add Symbol Export List (HIGH IMPACT)
**Expected reduction: 100-130 MB**

Instead of `--whole-archive`, create an explicit symbol export list of runtime functions actually needed by the generated code. The linker will pull only the needed archive members.

```
# In native_project.rs, replace:
cmd.arg("-Wl,--whole-archive")
# With:
cmd.arg("-Wl,--undefined=rt_symbol1")
cmd.arg("-Wl,--undefined=rt_symbol2")
# ... for each runtime function referenced by codegen
```

Alternative: Generate a linker version script that lists required symbols.

**Why `--whole-archive` was added:** The interpreter dispatch table and vtable lookups use string-based symbol resolution at runtime. The linker can't see these references. Fix: emit a list of all runtime symbols referenced by the dispatch tables as explicit `--undefined` linker flags.

### Fix 2: Add `-ffunction-sections -fdata-sections` to Normal Builds (MEDIUM IMPACT)
**Expected reduction: 10-30% after Fix 1**

**File:** Add to the C backend compilation flags in the normal (non-baremetal) build path, mirroring what `baremetal.spl:222-223` already does.

### Fix 3: Enable LTO for Native Builds (MEDIUM IMPACT)
**Expected reduction: 20-40% after Fix 1+2**

Pass `-flto=thin` to both compile and link steps. Thin LTO is fast enough for development; fat LTO for release builds.

### Fix 4: Strip by Default for Release Builds (LOW-HANGING FRUIT)
**Expected reduction: 30-60%**

Change `strip: false` default in `linker_wrapper.spl:386` to `strip: true` when `--release` is set. Or always pass `-Wl,-s` in release mode.

### Fix 5: Separate Runtime Libraries (LONG-TERM)
Split `libsimple_runtime.a` (133 MB monolith) into functional groups:
- `libsimple_rt_core.a` — essential runtime (memory, strings, I/O)
- `libsimple_rt_net.a` — networking
- `libsimple_rt_compiler.a` — compiler-specific runtime
- `libsimple_rt_gpu.a` — CUDA/GPU runtime

MCP servers would link only `libsimple_rt_core.a` + `libsimple_rt_net.a`.

### Fix 6: Demand-Driven Compilation (LONG-TERM)
Instead of loading all 4,527 source files when `has_project_source` is true, implement reachability analysis from the entry point. Only compile functions that are transitively reachable. This is what Zig does and it's the most effective solution.

---

## 5. Summary: Why It "Always Happens"

```
18 .spl files (T32 MCP)
    ↓ native-build
    ↓ compiled to C, linked with libsimple_runtime.a
    ↓ --whole-archive forces ALL 133 MB of runtime in
    ↓ no -ffunction-sections → gc-sections can't remove anything
    ↓ no LTO → no cross-module dead code elimination
    ↓ not stripped → debug info adds 30-60%
    = 177 MB binary
```

The linker **cannot** fix this because `--whole-archive` explicitly tells it "include everything." The problem is in the build pipeline, not the linker. The linker is doing exactly what it's told.

**The fundamental issue:** The Simple native build treats every binary as a whole-program build. There's no mechanism to build a "slim" binary that includes only what's reachable from the entry point. Every native binary gets the full runtime, full stdlib, and (if triggered) full compiler — regardless of what it actually uses.

---

## 6. Quick Win Estimate

| Fix | Effort | Expected Size After |
|-----|--------|-------------------|
| Strip only | 1 line | ~90-100 MB |
| Strip + remove `--whole-archive` | 1 week | ~20-40 MB |
| + `-ffunction-sections` + LTO | 2 days | ~10-20 MB |
| + split runtime | 2 weeks | ~5-10 MB |
| + demand-driven compilation | months | ~2-5 MB |
