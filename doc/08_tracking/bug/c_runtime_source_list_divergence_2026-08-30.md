# C runtime source-list divergence — independent verification (2026-08-30)

Follow-up to `doc/08_tracking/bug/rt_symbol_census_windows_2026-08-30.md`.
Read-only analysis. Every set below was computed mechanically (extractor:
start-of-line C definitions of `rt_*`; `static`/`extern`/`typedef` and
declaration lines excluded; unity `#include "*.c"` expanded; `src/runtime/vendor/**`
and the three `stb_*`/`miniaudio` headers excluded per CLAUDE.md Owned-Code Scope).

## 0. CORRECTION: there are THREE lists, not two

The census compares two. A third exists and changes the interpretation:

| # | list | file | .c entries | rt_* symbols | what it feeds |
|---|---|---|---|---|---|
| 1 | seed core-C | `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:337-412` | 15 uncond. + 4 gated | 855 | `build_c_runtime_library()` -> `libsimple_runtime.a` (core-C capsule) |
| 2 | pure-Simple backend | `src/compiler/70.backend/backend/runtime_compiler.spl:366` | 25 uncond. + 2 gated | 1110 | `compile_runtime_objects()` -> objects on every self-hosted native link |
| 3 | Rust runtime crate | `src/compiler_rust/runtime/build.rs:228-341` | 23 uncond. + 1 gated | 362 | C objects inside the Rust runtime staticlib -> the **seed binary / interpreter**, and `libsimple_native_all.a` |

List 3 is why several of these gaps are invisible in day-to-day use: the
interpreter resolves them from code linked into the seed binary itself.

**It does not rescue the self-hosted native lane.**
`llvm_native_link_orchestrator.spl:112-127` links `libsimple_native_all.a`
only when `SIMPLE_RUNTIME_PATH` is set, `stage4` is not requested, and the
build is not cross — and the comment at `:128-140` is explicit that it is a
**backfill** for seed-owned externs, never a replacement. A plain self-hosted
`native-build` therefore links **only list 2's objects**. So the census's
concern stands; list 3 only explains why the failures are latent.

## 1. Verified bucket counts (file level, lists 1 vs 2)

`.c` files under `src/runtime/`, vendored excluded: **120** (78 non-test).

| bucket | count | files |
|---|---|---|
| seed-only | 5 | `hosted_cocoa.c`, `hosted_win32.c`, `runtime_https_openssl_core.c`, `runtime_sqlite.c`, **`runtime_terminal.c`** |
| Simple-only | 13 | `runtime.c`, `runtime_audio.c`, `runtime_dynload.c`, `runtime_glfw.c`, `runtime_image.c`, `runtime_renderdoc.c`, `runtime_rocm.c`, `runtime_sdl2.c`, `runtime_sdl3.c`, `runtime_simd_search.c`, `runtime_socket_nonblock.c`, `runtime_timestamp.c`, `counterpart_abi_runtime.c` |
| both | 14 | — |
| **neither** | **88** | 42 `test/`, 11 `startup/baremetal/`, 6 `scilib/`, 6 `platform/`, 4 other `startup/`, 1 `sffi/`, **16 top-level** |

Note the seed's own `find_core_c_runtime_source_root()` probes for `runtime.c`
but never compiles it — `runtime.c` is Simple-list-only.

## 2. Symbol-level counts (this CORRECTS the census)

| metric | census | measured here |
|---|---|---|
| seed list `rt_*` | ~745 | **855** |
| Simple list `rt_*` | ~1024 | **1110** |
| in neither list | 235 | **163** |
| union | — | 1179 |
| in both | — | 786 |
| seed-only symbols | — | 69 |
| Simple-only symbols | — | 324 |
| symbols across ALL non-vendored `.c` (incl. `test/`) | — | 1342 |

The census's 235 is high by ~72. Two causes found: (a) `runtime_contracts.c`
unity-includes `runtime_any_ops.c` and `runtime_string_ffi.c`, so those two
files' symbols ARE compiled by both lists despite neither file appearing in
either list; (b) declaration lines and `static` helpers appear to have been
counted as definitions. Direction and severity are unchanged — 163 uncompiled
symbols is still a real population.

## 3. Referenced-but-uncompiled, ranked (task 2)

References = literal `extern fn rt_...` / call sites in `src/lib`, `src/compiler`,
`src/app` (`*.spl`). **114 referenced `rt_*` symbols are absent from the Simple
list**, i.e. undefined on the default self-hosted native lane:

| rank | file | syms | in list 3 (Rust crate)? | verdict |
|---|---|---|---|---|
| 1 | **`runtime_terminal.c`** | 6 | no C; Rust twin in `env_process.rs` | **REAL GAP — actionable** |
| 2 | `runtime_db.c` | 21 | **yes** | real gap on the self-hosted lane only |
| 3 | `runtime_coverage_core.c` | 6 | **no** | compiled by NO lane at all |
| 4 | `runtime_sqlite.c` | 27 | no | deliberate (needs sqlite3 SDK; seed stage4-gated) |
| 5 | `scilib/*.c` (openblas/mock/cublas/cusolver) | 73 | no | deliberate — separate BLAS/CUDA shim lib |
| 6 | `startup/baremetal/runtime_minimal.c`, `startup/baremetal/runtime_log.c` | 14 | no | deliberate — SimpleOS/baremetal lane |
| 7 | `startup/common/runtime_log_hosted.c` | 5 | **yes** | documented follow-up (nested path) |
| 8 | `platform/async_driver.c` | 4 | no | nested path; same blocker as 7 |
| 9 | `runtime_https_openssl_core.c` | 6 | no | deliberate (OpenSSL, env-gated in seed) |
| 10 | `runtime_memory.c` | 2 | **yes** | `rt_ptr_read_i32`, `rt_mem_harden_check_native` |
| 11 | `hosted_win32.c` / `hosted_cocoa.c` | 2 | partly | target-gated by design |

Symmetric gap on the seed core-C side (358 referenced symbols missing), led by
`runtime_sdl2.c` (86), `runtime_glfw.c` (39), `runtime.c` (34),
`runtime_audio.c` (32), `runtime_rocm.c` (31), `runtime_timestamp.c` (14),
`runtime_simd_search.c` (1). The seed core-C capsule is deliberately minimal,
so most of these are by design; `runtime.c` and `runtime_timestamp.c` are the
surprising ones and deserve their own look.

## 4. Deliberate omissions — do NOT "fix" these (task 3)

Each is documented in-tree; the evidence is cited, not asserted.

- **`runtime_pool.c` (64 `rt_pool_*` symbols).** `tools.rs` comment:
  *"runtime_thread.c owns both rt_thread_* and rt_pool_*; compiling
  runtime_pool.c beside it would create duplicate pool definitions."*
  Verified: `runtime_thread.c` is in BOTH lists. Not a gap — a duplicate.
- **`test/**` (42 files).** Self-check TUs; several unity-include the real
  `.c` they test. Never build inputs.
- **`startup/baremetal/**` (11).** SimpleOS/freestanding lane, built by the OS
  build, not by hosted native-build. Linking them hosted would collide.
- **`scilib/**` (6).** BLAS/LAPACK/cuBLAS/cuSolver shims; `openblas_shim.c`
  unity-includes `mock_shim.c`. External SDKs. Separate lane.
- **`runtime_sqlite.c` / `runtime_https_openssl_core.c`.** Explicitly gated in
  the seed (`include_stage4_hosted`, `SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL=1`).
  Heavy optional deps — intentional.
- **`counterpart_worker_runtime.c`, `scv_wasm_shim.c`.** Known external-SDK
  SKIPs (`wasmtime.h` et al.) per `.claude/rules/vcs.md`; they define 0 `rt_*`.
- **`startup/common/runtime_log_hosted.c`, `platform/*.c`, `sffi/*.c`.** Not an
  oversight: `runtime_compiler.spl:355-362` states the flat `{rt_dir}/{name}.c`
  naming cannot express a nested path without also teaching the object-path
  builder to create nested directories — *"left as a follow-up, not silently
  dropped."* Adding these needs that mechanism first, not a list edit.
- **`hosted_cocoa.c` / `hosted_win32.c`.** Deliberately target-conditional in
  both list 1 (`tools.rs:398-402`, Linux-only, so live Cocoa/Win32 calls
  fail closed rather than becoming generated stubs) and list 3
  (`build.rs:339`, `target_os != "windows" && !native_all_provider`).

## 5. Minimal reconciliation proposal (task 4)

### P1 — ADD `runtime_terminal.c` to the pure-Simple list (IMPLEMENTED)

Fixes: `rt_terminal_is_tty`, `rt_terminal_stdout_is_tty`,
`rt_terminal_enable_raw_mode`, `rt_terminal_disable_raw_mode`,
`rt_terminal_get_size`, `rt_stdin_read_byte` — declared `extern fn` in
`src/lib/nogc_sync_mut/tui/terminal.spl:42-47` and re-declared in
`src/app/office/interactive.spl:394-396`,
`src/app/office/sheets/calc_session_host.spl:16`,
`src/app/office/sheets/calc_access_session_host.spl:16-17`. Today a self-hosted
native build of anything reaching `std.tui.terminal` links with these
undefined — the tolerated-undefined -> NULL-GOT SIGSEGV class of
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.
(`rt_terminal_size_tuple` is also defined there but has no `.spl` reference.)

**Linux/macOS risk: low, and argued mechanically —**
1. *It compiles on Linux.* `tools.rs` compiles `runtime_terminal.c`
   **unconditionally, on every target**, in the core-C capsule already, and
   that lane is gated green by `check-c-runtime-compiles-push.shs`. Its POSIX
   branch includes only `<errno.h> <sys/ioctl.h> <termios.h> <unistd.h>` — no
   new link flags, no SDK.
2. *No collision inside list 2.* Its 7 defined symbols were diffed against the
   union of all 26 existing Simple-list members' definitions: **empty
   intersection**. It is the **sole** `.c` definer of all 7 anywhere in
   `src/runtime`.
3. *No new collision with `libsimple_native_all.a`.* Rust also defines
   `rt_terminal_is_tty`/`rt_stdin_read_byte` (`env_process.rs:1591,1626`) —
   but **383 `rt_*` symbols are already defined by both the Rust runtime and
   list 2's C files**, including 7 from that very same `env_process.rs` TU
   (`rt_exit`, `rt_platform_name`, `rt_process_wait`, `rt_process_kill`,
   `rt_process_is_running`, `rt_term_enable_ansi`, `rt_lexer_source_slice`).
   The orchestrator comment at `:128-140` documents the mechanism: the fresh
   C runtime owns the symbol, the archive backfills only still-undefined ones.
   This adds no new collision class.
4. *Windows.* Its `#ifdef _WIN32` branch (`<windows.h>`, `<io.h>`) is what
   makes the file portable; that branch is what the Windows census flagged.

Behaviour change on Linux: a self-hosted native binary that previously linked
with 6 undefined symbols now resolves them to the same implementations the
seed core-C lane and the interpreter already use. Nothing else moves.

5. *Measured, not only inferred.* `clang -fsyntax-only -Isrc/runtime
   src/runtime/runtime_terminal.c` on the Windows host (clang, MSVC ABI,
   Windows Kit 10.0.26100) exits **0**; the single warning is a pre-existing
   `strdup` deprecation in `runtime_memtrack.h`, a header both lists already
   compile. This exercises the `_WIN32` branch — the one the Simple lane had
   never built — so the compile step of this change is measured on the
   riskiest host, not assumed. The POSIX branch is covered by the seed's
   unconditional core-C compile, gated green by
   `check-c-runtime-compiles-push.shs`.
6. *Stage4 is unaffected.* The strict-Stage4 path repackages `runtime_objects`
   into named provider archives (`runtime_native`, `process`, `dynload`,
   `font`, `memtrack`, `time`, `fork`, `contracts`, `legacy_compat`), each
   selected by stem via `stage4_runtime_provider_object_matches`. An object
   matching no provider stem is simply not packaged — the existing list already
   contains many such objects (`runtime_glfw`, `runtime_sdl2`, `runtime_sdl3`,
   `runtime_audio`, `runtime_rocm`, `runtime_renderdoc`, ...). No
   exhaustiveness check over `runtime_objects` exists, so nothing new fails.

Edit shape: `runtime_terminal` must be appended to BOTH the `sources` array and
the parallel `objects` array in `compile_runtime_objects` at the **same index** —
the loop indexes `objects[object_count]` positionally.

### P2 — NOT IMPLEMENTED, needs a link test: `runtime_db.c`

21 referenced `rt_db_*` (`src/lib/nogc_sync_mut/database/fast_db.spl`).
Pure `<stdint/stdlib/string/stdio>`, no SDK, already in list 3 so it compiles
on Linux today. Left unimplemented because 21 symbols is a materially larger
surface than P1 and the duplicate-vs-Rust question was not re-verified per
symbol here; a bootstrap link is the honest gate and one is running elsewhere.

### P3 — NOT IMPLEMENTED, file a separate record: `runtime_coverage_core.c`

6 referenced `rt_coverage_*`, compiled by **no lane at all** (absent from all
three lists). `src/lib/nogc_sync_mut/ffi/coverage.spl:8` declares it returning
`bool?`, which suggests the nil-on-missing path is being relied on — exactly
the silent-nil class of `unregistered_extern_silent_nil_2026-08-01.md`. Needs
a decision (wire it, or delete the externs), not a list edit.

### P4 — NOT PROPOSED

Everything in §4. In particular do not add `runtime_pool.c` (duplicate),
any `startup/`/`platform/` path (blocked on nested-path support, documented),
or any SDK-gated file.

## 6. Suggested guard follow-up

Nothing today compares these three lists. A cheap fail-closed check — "every
`rt_*` symbol with an `extern fn` declaration in `src/{lib,compiler,app}` is
defined by at least one member of list 2" — would have caught
`runtime_terminal.c`, `runtime_simd_case.c` (fixed the same way earlier), and
`runtime_coverage_core.c`. Not implemented here.
