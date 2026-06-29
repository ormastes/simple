# Bootstrap Crash Report — 2026-04-01

## Summary

The bootstrap pipeline crashed with **OOM (SIGKILL, exit 137)** at Stage 2 after the Rust seed compiler build completed. Memory grew linearly at **3.7 GB/5sec**, reaching **118 GB** peak RSS before being killed. The crash occurred in the `--backend llvm-lib` code path, which dispatches native-build through the Simple interpreter instead of the Rust-native handler.

## Crash Location

| Field | Value |
|-------|-------|
| **Stage** | Stage 2: seed → bootstrap_main.spl |
| **Signal** | SIGKILL (9) — OOM killer |
| **Exit code** | 137 |
| **Peak RSS** | 124,397,660 KB (118 GB) |
| **Growth rate** | ~3.7 GB every 5 seconds (~740 MB/sec) |
| **Last log output** | `[native-build] dispatching to Simple app: src/app/cli/bootstrap_main.spl` |
| **Command** | `seed native-build --backend llvm-lib --entry-closure --entry bootstrap_main.spl` |

## Root Cause Chain (3 cascading issues)

### 1. Missing `--entry-closure` in bootstrap_main.spl

**File:** `src/app/cli/bootstrap_main.spl` (function `run_pure_simple_native_build`)

The `--entry-closure` CLI flag is NOT parsed or forwarded. When `--backend llvm-lib` is used, the seed dispatches to the Simple interpreter which runs `bootstrap_main.spl`. This code calls `aot_native_project_with_backend(source_dirs, entry, output, backend, strip)` — a function that does NOT accept an `entry_closure` parameter.

**Result:** Instead of compiling the **100 reachable files** from the entry closure, the compiler scans ALL source directories and attempts to compile **3,573 files**.

### 2. Stale `libsimple_native_all.a` (no `--entry-closure` in `rt_native_build`)

**File:** `src/compiler_rust/native_all/src/lib.rs` (function `rt_native_build`)

The Cranelift code path falls through to `rt_native_build(args)` which IS in the runtime library but the compiled library was **stale** (March 28 build vs March 31 source modification). The stage2 binary's `rt_native_build` printed:

```
warning: unknown option '--entry-closure', ignoring
```

**Evidence:** `strings libsimple_native_all.a | grep -c entry-closure` = 0 (before fix)

The bootstrap script's stale detection only checks the seed binary timestamp, not the static library. The library has hardlink count=2 causing misleading mtime.

### 3. LLVM Context memory leak (`Box::leak`)

**File:** `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs:67`

```rust
let context = Box::leak(Box::new(Context::create()));
```

Each file compiled creates a new LLVM `Context` that is intentionally leaked via `Box::leak`. With 3,573 files compiled in parallel (rayon), all contexts accumulate simultaneously in memory. Each context holds LLVM IR, module metadata, and type caches.

**Impact:** 3,573 leaked LLVM Contexts × ~30-40 MB each ≈ 118 GB → OOM

### 4. Additional issue: C++ TLS stub mismatch (discovered during fix)

**File:** `src/compiler_rust/compiler/src/pipeline/native_project.rs` (function `generate_stub_object`)

When rebuilding `libsimple_native_all.a`, the M68k LLVM backend object (`M68kCollapseMOVEMPass.cpp.o`) contains a TLS (thread-local storage) reference to `_ZSt11__once_call`. The stub generator creates non-TLS stubs, causing linker error:

```
TLS reference in libsimple_native_all.a(M68kCollapseMOVEMPass.cpp.o) mismatches non-TLS definition in _stubs.o
```

### 5. Additional issue: LLVM option conflict in self-hosted binary (LIM-010)

Stage2 binary crashes at startup with:
```
CommandLine Error: Option 'debug-counter' registered more than once!
LLVM ERROR: inconsistency in registered CommandLine options
```

Static LLVM objects in `libsimple_native_all.a` register CLI options at load time; with C++ symbols resolved (not stubbed), these constructors run and conflict.

## Fixes Applied

| Fix | File | Description |
|-----|------|-------------|
| Default backend → cranelift | `scripts/bootstrap/bootstrap-from-scratch.sh` | Avoids the llvm-lib interpreter dispatch path entirely |
| Stage 3 non-fatal + exit 2 | `scripts/bootstrap/bootstrap-from-scratch.sh` | Stage3 self-host is optional; falls back to seed for stage4; exits with code 2 (not 0) when self-host fails |
| LLVM env var | `scripts/bootstrap/bootstrap-from-scratch.sh` | `LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1` on stage3/4 |
| C++ TLS stub filter | `src/compiler_rust/compiler/src/pipeline/native_project.rs` | `_ZSt*`/`_ZNSt*` symbols excluded from stub generation to prevent TLS mismatch |
| LLVM constructor stripping | `src/compiler_rust/compiler/src/pipeline/native_project.rs` | `strip_llvm_constructors()` removes `.init_array`/`.ctors` from all `*.cpp.o` in the archive via `objcopy` to prevent SIGSEGV at startup (LIM-010 fix) |
| FreeBSD linker flags | `src/compiler_rust/common/src/platform/link_config.rs` | Added `--unresolved-symbols=ignore-all` to FreeBSD config (matching Linux) |
| Dockerfile.bootstrap | `tools/docker/Dockerfile.bootstrap` | Added `libunwind-dev` for linker |

## Verification

Full bootstrap completed in Docker (Ubuntu 24.04, 32 GB memory limit):

```
Stage 2: seed → bootstrap_main.spl     ✓ (100 files, 0.8s compile)
Stage 3: stage2 → bootstrap_main.spl   ✓ (100 files, 0.8s compile — SELF-HOST WORKS)
  stage2 SHA256 == stage3 SHA256        ✓ (REPRODUCIBLE BUILD)
Stage 4: stage3 → main.spl             ✓ (135 files, 0.9s compile)
Final binary: 149 MB ELF x86-64
Exit code: 0
```

## Prevention Recommendations

1. **Add `entry_closure` to Simple `CompileOptions`** — `bootstrap_api.spl` and `bootstrap_main.spl` should support `--entry-closure` natively so both llvm-lib and cranelift paths use it.

2. **Fix bootstrap stale detection** — Check `libsimple_native_all.a` timestamp in addition to the seed binary. Hardlinks mask true mtime.

3. **Fix LLVM Context leak** — Implement `Drop` for `LlvmBackend` that reclaims the `Context` instead of `Box::leak`, or use a thread-local context pool with bounded concurrency.

4. **Add memory limit to bootstrap script** — Use `ulimit -v` or Docker `--memory` to fail fast instead of consuming all system RAM.
