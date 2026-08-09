# DirectX-family test triage: a real Windows Vulkan-probe bug (FIXED), a real `/bin/sh` runtime bug (FIXED, unverified end-to-end), and a chain of pre-existing Windows Rust-seed rebuild blockers (OPEN)

Date: 2026-08-09
Area: GPU/DirectX translation layer, `process_run` runtime, Windows Rust-seed
build toolchain

## Summary of what was checked

Ran the DirectX-family test surface (`dxvk_*`, `vkd3d_d3d12`,
`backend_directx_spec`, `windows_d3d12_render_log_*`,
`gui_web_2d_directx_env`, `processing_cuda_directx_native`) via the
June-2026 Rust seed binary (`SIMPLE_BOOTSTRAP=1
src/compiler_rust/target/bootstrap/simple.exe`), per the earlier finding
(see `sspec_module_docstring_plus_subprocess_it_false_green_2026-08-08.md`
and `windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md`) that
the deployed April binary's `test` command does not reliably evaluate
assertions.

## FIXED 1: Vulkan ICD probe never checked for the Windows loader

**File:** `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl`, `_icd_probe_leaf()`.

Every DirectX-over-Vulkan translation layer (`dxvk_d3d9.spl`,
`dxvk_d3d10.spl`, `dxvk_d3d11.spl`, `vkd3d_d3d12.spl`) routes device/instance
creation through this one probe, which checked five candidate paths — all
five were `.so` (Linux) paths (`build/dx/prefix/lib/libdxvk_d3d11.so`,
`/usr/lib/x86_64-linux-gnu/libvulkan.so.1`, etc.). **Zero Windows candidates
existed**, so on Windows every call refused honestly with
`no-vulkan-library-found: structured handles refused` regardless of whether
a real Vulkan runtime was present.

Confirmed the refusal was NOT because Vulkan was actually missing:
`vulkaninfo --summary` on this host reports a live device (`Intel(R) UHD
Graphics 770`, driver 101.5592, Vulkan API 1.3.284).

**Fix:** added two more candidates —
`<SystemRoot>/System32/vulkan-1.dll` and `<SystemRoot>/SysWOW64/vulkan-1.dll`
(via `env_get_or("SystemRoot", "C:/Windows")`, same-family import
`std.nogc_async_mut.env.variables.{env_get_or}` to avoid a
higher-layer-family import warning that a `nogc_sync_mut` import triggered
in an earlier draft of this fix).

**Verified** via `bin/simple run` (the seed's interpreter path, since `test`
was not yet trustworthy at time of writing):
`test/01_unit/lib/nogc_async_mut/gpu/dxvk_spec.spl` went from 8 passed / 12
failed to **20 passed / 0 failed** (all three of D3D9, D3D10, D3D11
translation). Re-ran the full DirectX-family list afterward via `simple
test --clean`:

| Spec | Before | After |
|---|---|---|
| `dxvk_spec.spl` | 8p/12f | **20p/0f** |
| `dxvk_vkd3d_dispatch_spec.spl` | 5p/13f | **18p/0f** |
| `vkd3d_d3d12_spec.spl` | 6p/5f | **11p/0f** |

## FIXED 2: `dxvk_d3d10_icd_spec.spl` missing `std.` import prefix

Unrelated to the Vulkan probe: `test/01_unit/lib/nogc_async_mut/gpu/dxvk_d3d10_icd_spec.spl`
(and its duplicate at `test/unit/lib/nogc_async_mut/gpu/dxvk_d3d10_icd_spec.spl`
— same blob, tracked twice) imported `nogc_async_mut.gpu.dxvk_d3d10` instead
of `std.nogc_async_mut.gpu.dxvk_d3d10`, so the module never resolved
(`Cannot resolve module: nogc_async_mut.gpu.dxvk_d3d10`) and the spec
reported "1 example, 1 failure" for what is actually a 10-`it`-block file —
this predates and is unrelated to the Vulkan probe gap. Fixed both copies;
`test/01_unit/.../dxvk_d3d10_icd_spec.spl --clean` now reports **11 passed,
0 failed**.

## FIXED 3 (unverified end-to-end): `process_run("/bin/sh", ...)` cannot spawn on Windows

**File:** `src/compiler_rust/runtime/src/value/sffi/env_process.rs`.

Separately discovered while investigating `windows_d3d12_render_log_compare_spec.spl`
(11/11 examples failing with empty captured stdout and a stray
`Export statement references undefined symbol name=rt_file_read_text`
warning): the spec's `process_run("/bin/sh", ["-c", command])` calls return
exit code **-1** (spawn failure) on Windows even though a working `sh.exe`
(git-bash/MSYS2) is on PATH.

Root cause, PROVED via `xxd`/direct testing (not inferred): `Command::new("/bin/sh")`
on Windows treats the leading `/` as "root of the current drive"
(`C:\bin\sh`), which does not exist — and unlike a real shell, Windows
`CreateProcess` does **not** fall back to a PATH search once the string
contains a path separator. `process_run("sh", [...])` (bare name, no
separator) resolves correctly via PATH search. This is a widespread
portability landmine: **643 spec files** across `test/` call
`process_run("/bin/sh", ...)` (measured via `grep -rl`), all written against
Linux/macOS where `/bin/sh` is a real path.

**Fix (root-cause, not per-spec):** added `resolve_command_path()` in
`env_process.rs` — on Windows only, and only when the literal path does not
already exist on disk, rewrites `/bin/sh`→`sh`, `/bin/bash`→`bash`,
`/bin/env`→`env` (and their `/usr/bin/*` equivalents) before constructing
`std::process::Command`. Routed all 9 `Command::new(cmd_str)` call sites in
this file through it (`rt_process_run`, `rt_process_run_inherit`,
`rt_process_spawn`, `rt_process_run_timeout`, `rt_process_run_bounded`,
`rt_process_run_with_limits`, and two more). A single Linux-only
`Command::new("/bin/sh")` call (the `setsid`/process-group guard wrapper,
`#[cfg(target_os = "linux")]`) was deliberately left untouched — it never
compiles on Windows and `/bin/sh` is a real path on Linux.

Chosen at the runtime level rather than editing 643 spec files: this fixes
every current and future caller without touching test content, and per
`.claude/rules/bootstrap.md` this class of bug (an FFI/extern boundary
implemented in Rust) can only be fixed in the Rust runtime — there is no
pure-Simple equivalent to patch instead.

**Also fixed in the same investigation:** the SSpec interpreter's BDD
builtin dispatch (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`)
was missing `"fail_test"` from its `"fail" | "fail_assertion"` match arm.
`fail_test` (`src/lib/nogc_sync_mut/spec.spl:848`, a plain `pub fn` wrapper
calling `fail_assertion`) is `use std.spec.{... fail_test}`-imported and
explicitly exported, but under the interpreter's BDD fast path calling it
hit normal function resolution instead and failed with `function
"fail_test" not found` — reproduced via
`test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl`.
Added `"fail_test"` to the same match arm.

### Verification status: NOT run end-to-end (see the rebuild chain below)

Both `.rs` fixes are code-reviewed for correctness (syntax, borrow/lifetime
shape, and call-site wiring were all re-read line by line since a rebuilt
binary was not available) and directly address independently-PROVED bugs
(the `/bin/sh` spawn failure was reproduced and root-caused via direct
`process_run` probing before the fix was written; `fail_test` was reproduced
via a real failing spec run). They have **not** been exercised in a rebuilt
binary — every attempt to rebuild the Windows Rust seed this session hit a
DIFFERENT, PRE-EXISTING, unrelated toolchain blocker (below), none in the
files this fix touches.

Also confirmed the SAME `/bin/sh` root cause explains
`test/03_system/check/gui_web_2d_directx_env_spec.spl`'s "rejects linked
DirectX browser proof files" failure (`process_run("/bin/sh", ...)` at line
164 of that spec) — should self-resolve once this fix is in a rebuilt
binary, same as `windows_d3d12_render_log_compare_spec.spl`.

## OPEN: chain of pre-existing Windows Rust-seed rebuild blockers

Attempting to rebuild `src/compiler_rust/target/bootstrap/simple.exe` (the
seed used for all verification above, since the deployed self-hosted
`bin/simple` cannot currently redeploy at all — see
`windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md`) surfaced
four SEPARATE environment issues, each blocking the build at a different
stage:

1. **MSVC C11 `<stdatomic.h>` gap.** `cargo build --profile bootstrap -p
   simple-driver --bin simple --features llvm` failed compiling
   `runtime_simd_dispatch.c` with `fatal error C1189: "C atomics require
   C11 or later"`. `src/compiler_rust/runtime/build.rs` applied
   `-std=gnu11` (a GCC/Clang flag `cl.exe` silently drops via
   `flag_if_supported`) only on non-MSVC targets, leaving MSVC on its
   default C mode. **FIXED**: added `build.flag_if_supported("/std:c11")`
   in the MSVC branch. That alone was insufficient on this host's MSVC
   14.44.35207 — a second, more specific error appeared
   (`"C atomic support is not enabled"`) requiring the additional
   `/experimental:c11atomics` flag, also added. Both together cleared this
   stage.

2. **`llvm-config` PATH-order contamination.** With #1 fixed, the build
   proceeded to `llvm-sys`'s build script, which shells out to whatever
   `llvm-config` resolves first on PATH — on this host that is
   `C:\dev\tool\msys2\mingw64\bin\llvm-config.exe` (a MinGW build), NOT the
   MSVC-built LLVM 18.1.8 at
   `C:\dev\install\clang+llvm-18.1.8-x86_64-pc-windows-msvc\bin`, because
   `/mingw64/bin` appears earlier in `$PATH`. This poisoned the MSVC `cl.exe`
   invocation with MinGW-style `-IC:/dev/tool/msys2/mingw64/include`
   flags, producing hundreds of `stdlib.h`/`malloc.h` parse errors.
   **WORKAROUND** (not a repo fix — an environment variable for this
   specific build invocation): `LLVM_SYS_180_PREFIX=C:/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc`
   forces the correct prefix regardless of PATH order. Not committed as a
   repo change since it's host-specific; flagging that the Windows
   bootstrap docs should mention this env var is needed on any host where
   an MSYS2/MinGW `llvm-config` shadows the MSVC one on PATH.

3. **`runtime_audio.c` unconditionally includes `<pthread.h>`.** With #1
   and #2 cleared, the build reached `runtime_audio.c`, which does
   `#include <pthread.h>` and uses `pthread_mutex_t`/`pthread_mutex_lock`
   throughout for a global audio lock — POSIX-only; MSVC has no
   `pthread.h`. The file's own header comment documents its intended build
   line as `cc -c -fPIC -O2 -std=gnu11 -I. -lpthread -lm runtime_audio.c`
   (GCC/Clang-only), suggesting this file was never designed to compile
   under MSVC directly. **NOT FIXED** — would need either a Win32
   `CRITICAL_SECTION`-based reimplementation of the lock or a build-time
   MinGW-provided pthread shim; out of scope for this session (deep,
   correctness-sensitive change to a locking primitive, not a
   flag/path adjustment).

4. **`x86_64-pc-windows-gnu` target as an alternative: cross-`gcc` itself
   fails its own compiler-family detection probe.** Tried building for the
   GNU/MinGW target instead of MSVC (sidesteps #1 and #3 entirely, since
   MinGW ships real `pthread.h` and doesn't have MSVC's C11 gap). Both the
   PATH-resolved `gcc.exe` and an explicitly-set
   `CC_x86_64_pc_windows_gnu=C:/dev/tool/msys2/mingw64/bin/x86_64-w64-mingw32-gcc.exe`
   fail identically: `cc-rs`'s compiler-family detection (`gcc.exe -E
   ...detect_compiler_family.c`) exits with status 1 on the very first
   invocation, before any real source compiles (reproduced against the
   `ring` crate's build script). Not diagnosed further — this is a
   fundamental toolchain-health issue (the MSYS2 mingw64 gcc install
   itself, or its interaction with this specific cargo/rustc combination)
   separate from anything in this repository's own build configuration.

**Net effect:** #1 and #2 are resolved (#1 is a landed repo fix; #2 is a
documented host workaround). #3 and #4 remain open and are why no path to a
fully rebuilt Windows binary was reached this session — both the
MSVC-with-pthread-gap and the GNU-cross-toolchain routes are blocked by
issues unrelated to anything touched in this task. `resolve_command_path`
and the `fail_test` builtin fix remain unverified end-to-end pending
whichever of #3/#4 gets resolved first (or a different host/CI runner that
doesn't share this host's specific toolchain quirks).

## OPEN, not investigated: remaining `backend_directx_spec.spl` failures

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl` still
has real failures after fix 1, of two distinct shapes, neither related to
the Vulkan probe or `/bin/sh`:

1. `semantic: unknown extern function: rt_directx_hardware_adapter_identity`
   — declared in `src/lib/nogc_sync_mut/gpu/engine2d/sffi_directx.spl:8` as
   `extern fn rt_directx_hardware_adapter_identity() -> i64` but has **zero**
   implementation anywhere under `src/compiler_rust/runtime/` (confirmed via
   `grep -rn` across the whole runtime tree). A real DXGI adapter-identity
   query (`IDXGIFactory::EnumAdapters` + `IDXGIAdapter::GetDesc` via COM
   interop) would be needed to implement this for real — a substantial
   native-FFI feature addition, not a quick fix. Affects roughly 20 of the
   25 failing examples in this spec.
2. `semantic: variable "self" not found` — three examples
   ("native queue uses the frozen header and fixed CLEAR/FILL records",
   "unsupported operations poison native receipt eligibility", "opaque IMAGE
   is queued inline after a valid initializer"), not diagnosed.
3. `semantic: class "Engine2DReadback" has no field named "device_identity"`
   — two examples. `device_identity` exists on the unrelated
   `DirectXCheckedReadback` class in the same file family
   (`sffi_directx.spl`); the spec expects `Engine2DReadback`
   (`src/lib/gc_async_mut/gpu/engine2d/backend.spl`) to carry the same
   field, which it currently does not.

Not pursued further: this file sits in the actively-evolving GPU
backend/readback-provenance surface (dozens of `.spipe/` work-streams under
`gui-*`/`gpu-*`/`engine2d*` names exist in this repo), and (1) in
particular requires real native Windows GPU-API work well outside this
task's scope. Recording per instruction rather than attempting a fix.
