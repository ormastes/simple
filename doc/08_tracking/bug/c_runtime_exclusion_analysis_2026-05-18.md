# C Runtime Exclusion Analysis

**Date:** 2026-05-18
**Last audited:** 2026-05-29 (follow-up pass — pty, math/random/error/config, contracts, regex_stub, equality, format, value, and env removed)
**Status:** Open — audit still tracks removable C runtime candidates and blocked removals.
**Context:** Pure Simple conversion project — which C files can be removed

## Removed (zero callers)

| C File | Symbols | Action |
|--------|---------|--------|
| `runtime_ctype.c` | `__is_alnum/alpha/digit/xdigit/space/lower/upper` | Deleted. Rust shim had zero pub fns. Removed from tools.rs. |
| `runtime_audio_effects.c` | `rt_audio_set_pitch` + 6 stubs | Deleted. Not in tools.rs. Zero .rs/.spl callers. |
| `runtime_hash.c` | `rt_fnv_hash` | Deleted 2026-05-27. `simple-runtime` now implements FNV-1a in Rust and the legacy Rust std hash shim computes FNV in Simple instead of declaring the C extern. Removed from the core-C native-project runtime input list. |
| `runtime_crypto.c` | `rt_constant_time_compare` | Deleted 2026-05-27. `simple-runtime` and interpreter dispatch both implement constant-time comparison in Rust/Simple runtime code; no native-project runtime input remains. |
| `runtime_base64.c` | `__c_rt_base64_encode`, `__c_rt_base64_decode` | Already deleted from disk (confirmed 2026-05-29). Was listed under Group B but the file is gone. `sffi/utils.rs` wraps both symbols; no C file callers remain. |
| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | Deleted 2026-05-29 after zero build refs were reconfirmed. `value/pty.rs` exports both symbols via `#[no_mangle]`; interpreter dispatch remains in `interpreter_extern/pty.rs`. |
| `runtime_math.c` | `rt_math_*` | Deleted 2026-05-29 after Rust replacements were promoted to exported C ABI symbols in `value/sffi/math.rs`; not in build inputs, SFFI dispatch table, or calls.rs. |
| `runtime_random.c` | `rt_random_*`, `__c_rt_random_hex_buf` | Deleted 2026-05-29 after Rust replacements for the public `rt_random_*` ABI were exported from `value/sffi/random.rs`; `__c_rt_random_hex_buf` had zero callers. |
| `runtime_error.c` | `rt_function_not_found`, `rt_method_not_found` | Deleted 2026-05-29 after Rust replacements were promoted to exported C ABI symbols in `value/sffi/error_handling.rs`; `runtime_native.c` still provides its own core-C implementation for the tiny-native bundle. |
| `runtime_config.c` | `rt_set_macro_trace`, `rt_is_macro_trace_enabled`, `rt_set_debug_mode`, `rt_is_debug_mode_enabled` | Deleted 2026-05-29 after Rust replacements were promoted to exported C ABI symbols in `value/sffi/config.rs`; not in build inputs. |
| `runtime_contracts.c` | `simple_contract_check`, `simple_contract_check_msg` | Deleted 2026-05-29 after Rust replacements were promoted to exported C ABI symbols in `value/sffi/contracts.rs`; calls.rs dispatch resolves the same symbols. |
| `runtime_regex_stub.c` | `sffi_regex_is_match/find/find_all/captures/replace/replace_all/split/split_n` | Deleted 2026-05-29 after the disabled-regex Rust stub was promoted to exported C ABI symbols in `value/sffi/regex_stub.rs`; the `runtime-regex` feature path already exports the real implementation. |
| `runtime_equality.c` | `rt_native_eq`, `rt_native_neq`, `rt_value_eq`, `rt_value_compare` | Deleted 2026-05-29 after `rt_value_eq` and `rt_value_compare` were promoted to exported Rust C ABI symbols in `value/sffi/equality.rs`; native equality wrappers were already exported. |
| `runtime_format.c` | `__c_rt_value_format_string`, `__c_rt_raw_u64_to_str`, `__c_rt_value_to_display_str` | Deleted 2026-05-29 after no callers for the legacy `__c_rt_*` helpers were reconfirmed; active formatting SFFI symbols are exported from `value/sffi/io_print.rs`. |
| `runtime_value.c` | `rt_value_int/float/bool/nil`, `rt_value_as_*`, `rt_value_is_*`, `rt_value_truthy`, `rt_value_type_tag`, `rt_is_error`, `rt_ptr_to_value`, `rt_value_to_ptr` | Deleted 2026-05-29 after Rust value helpers and pointer conversion helpers were promoted to exported C ABI symbols in `value/sffi/value_ops.rs` and `value/sffi/memory.rs`; `runtime_value.h` remains as a C ABI header. |
| `runtime_env.c` | `__c_rt_env_*`, `__c_rt_exit`, `__c_rt_stdout_flush`, `__c_rt_stderr_flush`, `__c_rt_platform_name`, `__c_rt_term_get_size` | Deleted 2026-05-29 after no callers for the legacy `__c_rt_*` helpers were reconfirmed; active env/process/platform/flush SFFI symbols are exported from `value/sffi/env_process.rs` and `value/sffi/io_print.rs`. |

## Cannot Remove (active Rust/codegen callers)

### Group A — Codegen hard deps (blocked by cross-module ABI)

Symbols emitted directly by codegen or referenced in `elf_utils.rs`/`runtime_sffi.rs`.
Cannot remove until native linker resolves them from Simple-compiled objects.

**Build inputs confirmed 2026-05-29** — three separate compile paths, none sweeps the whole runtime dir:
- `runtime/build.rs` `c_sources[]`: `runtime_memory.c`, `runtime_time.c`, `runtime_db.c`
- `tools.rs` `build_core_c_runtime_library` `runtime_inputs[]`: `runtime_native.c`, `runtime_legacy_core.c`, `runtime_mcp_core.c`, `runtime_simd_utf8.c` (+ conditional `runtime_https_openssl_core.c`)
- `lib/build.rs`: only `src/io/term/nat/term_native.c` — unrelated

No other build.rs compiles any `src/runtime/*.c` file. Neither `runtime.c` nor `runtime_native.c` includes other `runtime_*.c` files (no amalgamation).

| C File | Key Symbols | Build Path | .spl Callers | Why It Stays |
|--------|-------------|------------|-------------|-------------|
| `runtime_memory.c` | `rt_alloc`, `rt_free`, `rt_ptr_read_i64/i32`, `rt_ptr_write_*`, `rt_memset`, `rt_memcpy` | `runtime/build.rs` c_sources | gpu/memory.spl, ptr/raw.spl, torch/sffi.spl, sffi/llvm_loader.spl | Codegen emits `rt_alloc` for every struct/array alloc; core ABI |
| `runtime_time.c` | 18 (`rt_time_*`, `rt_timestamp_*`) | `runtime/build.rs` c_sources | **199 files** | Most used runtime module; syscall wrappers |
| `runtime_native.c` | `rt_print`, `rt_println`, `rt_stdout_write`, `rt_stderr_write`, `rt_stdin_read_line`, `rt_string_new/len/data`, `rt_native_eq`, `rt_interp_call`, `rt_to_string`, etc. | `tools.rs` runtime_inputs | 0 direct (exposed via `use std.*`) | Foundation of the runtime ABI — strings, I/O, value boxing |
| `runtime_string_index.c` | `rt_swi_build/char_to_byte/byte_to_char/free`, `rt_rank_select_build`, `rt_rank_query`, `rt_select_query`, `rt_rank_select_free` | `codegen/runtime_sffi.rs` (8 entries), `interpreter_extern/simd.rs` | 0 direct | Codegen SFFI table + interpreter extern; Unicode index structures. **Not in any build.rs c_sources or tools.rs runtime_inputs** — linked via SFFI dispatch only; removability pending SFFI audit. |
| `async_driver.c` | `rt_driver_create/destroy`, `rt_driver_submit_*` (13 variants), `rt_driver_poll*`, `rt_driver_cancel` | `codegen/runtime_sffi.rs` (15 entries), `codegen/instr/calls.rs`, `llvm/functions/calls.rs` | 0 direct spl; driven via codegen SFFI | Async I/O driver; codegen emits all submit/poll calls |

### Group A2 — On-disk but NOT in any build input (removal candidates pending SFFI/codegen audit)

All files in this candidate group have now been audited and removed or shown to
be stale exact-ABI compatibility shims (verified 2026-05-29). `runtime_value.h`
remains on disk because remaining C runtime sources include it as an ABI header.

Verified blocker categories (2026-05-29 follow-up pass):
- **SFFI dispatch table** (`codegen/runtime_sffi.rs`): former `rt_value_*` and `rt_env_*` blockers now resolve to exported Rust replacements.
- **`calls.rs` codegen dispatch**: `simple_contract_check`, `simple_contract_check_msg`, and `sffi_regex_*` resolve to Rust exports now; the stale C files were deleted.
- **Interpreter extern Rust FFI** (`interpreter_extern/math.rs`): `rt_math_*` symbols are resolved from the Rust `simple-runtime` crate directly — NOT from the deleted C file. Same for pty.
- **Core-C tiny-native lane** (`build_core_c_runtime_library` in `native_project/tools.rs`): confirmed runtime_inputs = `[runtime_native.c, runtime_legacy_core.c, runtime_mcp_core.c, runtime_simd_utf8.c]` plus optional `runtime_https_openssl_core.c`. This lane keeps its own `rt_function_not_found` implementation in `runtime_native.c`; it did not require the deleted `runtime_error.c`.
- **C file count after removals:** 25 top-level `src/runtime/*.c` files remain.

| C File | Key Symbols | Rust Replacement | .spl Callers | Confirmed Blocker |
|--------|-------------|-----------------|-------------|---------|
| _none_ | _n/a_ | _n/a_ | _n/a_ | Group A2 completed 2026-05-29. |

### Group B — SPL FFI surface (blocked by no Simple replacement yet)

Symbols called from `.spl` extern declarations. Cannot remove until a pure-Simple
or Rust-only replacement is wired through the same symbol name.

| C File | Key Symbols | .rs Callers | .spl Callers | Why It Stays |
|--------|-------------|-------------|-------------|-------------|
| `runtime_audio.c` | `rt_audio_init/shutdown/load_sound/unload_sound/play/play_looped/stop/pause/resume/set_volume/set_master_volume/get_master_volume/is_playing` + spatial fns | 0 Rust codegen | `nogc_sync_mut/io/audio_sffi.spl` | miniaudio wrapper; spl audio layer |
| `runtime_font.c` | `rt_font_load/free/glyph_bitmap/bitmap_width/bitmap_height/bitmap_data/bitmap_free` | 0 Rust codegen | `nogc_sync_mut/io/font_sffi.spl` | stb_truetype wrapper |
| `runtime_fork.c` | `rt_fork_child_setup`, `rt_fork_parent_wait/stdout/stderr`, `rt_fork_child_exit` | 0 Rust codegen | `nogc_sync_mut/test_runner/test_runner_fork.spl` | Test runner fork isolation |
| `runtime_image.c` | `rt_image_load/free/width/height/channels/get_pixel` | 0 Rust codegen | `nogc_sync_mut/io/image_sffi.spl` | stb_image wrapper |
| `runtime_memtrack.c` | `spl_memtrack_enable/disable/is_enabled/record/unrecord/snapshot/dump_since/live_count/live_bytes/reset/count_since/bytes_since/set_listener/clear_listener` | 0 Rust codegen | `nogc_sync_mut/mem_tracker/mod.spl` | Memory leak tracking |
| `runtime_process.c` | `rt_process_spawn_piped`, `rt_process_write_stdin/read_stdout/is_alive`, `rt_editor_spawn/start/poll/wait_simple_dap` | 0 Rust codegen | 10+ spl files via `rt_process_run` | Shell out; used by db, io, env modules |
| `runtime_sdl2.c` | `rt_sdl2_init/quit/create_window/destroy_window/…` | 0 Rust codegen | `nogc_sync_mut/io/window_sffi.spl` | SDL2 windowing |
| `runtime_simd_case.c` | `rt_simd_case_*` | `codegen/runtime_sffi.rs`, `interpreter_extern/simd.rs` | 0 direct | Case-folding SIMD dispatch |
| `runtime_simd_dispatch.c` | `simd_crypto_init` + scalar stubs for aes/sha256/chacha20/crc32/ghash | 0 Rust codegen | 0 direct spl | Crypto dispatch table; referenced via `runtime_simd_dispatch.h` includes |
| `runtime_simd_search.c` | `rt_simd_search_*` | `codegen/runtime_sffi.rs`, `interpreter_extern/simd.rs` | 0 direct | String search SIMD |
| `runtime_simd_utf8.c` | `rt_simd_utf8_*`, SIMD text dispatch init | `codegen/runtime_sffi.rs`, `interpreter_extern/simd.rs` | 0 direct | UTF-8 validation/length SIMD |
| `runtime_thread.c` | `spl_thread_create/join/detach/current_id/sleep/yield/cpu_count/pool_spawn_worker`, `spl_mutex_*`, `spl_condvar_*` | 0 Rust codegen | `nogc_async_mut/thread_sffi.spl`, `thread_pool.spl` | Threading primitives |
| `runtime.c` | Bootstrap `spl_*` symbol set (spl_nil, spl_bool, spl_str, spl_array_*, spl_dict_*, spl_print*, spl_shell*, spl_malloc/free, rt_str_hash, …) | Bootstrap compiler stage only | 0 spl | Legacy bootstrap runtime; not linked in self-hosted build but must stay for stage0/stage1 |
| `scv_wasm_shim.c` | `wasm_rt_load`, `wasm_rt_free`, `wasm_rt_parse_all` | 0 Rust codegen | `src/lib/scv/wasm_executor.spl` (3 callers) | SCV grammar parsing via WASM tree-sitter |

### Group C — Newly Tracked (first appeared since 2026-05-18 audit)

Discovered on-disk 2026-05-29. These files were not in any previous audit pass.

| C File | Key Symbols | Build Path | Callers | Notes |
|--------|-------------|------------|---------|-------|
| `runtime_db.c` | `rt_db_table_create/destroy`, `rt_db_put/get/delete/scan_range`, `rt_db_row_count/col_count`, `rt_sqlite_*` (SQLite wrapper) | `runtime/build.rs` c_sources | `app/io/sqlite_sffi.spl`, `lib/nogc_sync_mut/database/sql/statement.spl`, `fast_db.spl`, `interpreter_extern/sffi_db.rs` | Active — SQLite wrapper with many spl callers. Cannot remove. |
| `runtime_legacy_core.c` | `spl_int`, `spl_str`, `spl_bool`, `spl_nil`, and minimal SplValue helpers for bridging `runtime_native.c` | `tools.rs` runtime_inputs | `runtime_native.c` (bridge only) | Minimal compatibility shim so `runtime_native.c` bridge fns link without pulling all of `runtime.c`. Cannot remove without restructuring `runtime_native.c`. |
| `runtime_mcp_core.c` | `rt_stdin_read_mcp_message_text` | `tools.rs` runtime_inputs | `tools.rs` native project | MCP stdio framing; used by native MCP server build. Cannot remove. |
| `runtime_https_openssl_core.c` | OpenSSL HTTPS helpers | `tools.rs` runtime_inputs (opt-in: `SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL=1`) | Optional HTTPS support | Conditional; only linked when env var set. Cannot remove. |
| `hosted_cocoa.c` | macOS Cocoa UI / window host | **Zero build refs on Linux** (confirmed 2026-05-29 — no `.rs` file outside vendor/ references it). `tools.rs` line 600 comment references `src/runtime/hosted/cocoa.rs` (a Rust file), not this C file. | macOS-specific | Status: not compiled on Linux; may be platform-gated macOS-only. Audit needed on macOS before declaring removable. |
| `hosted_win32.c` | Win32 UI / window host | **Zero build refs on Linux** (confirmed 2026-05-29). | Windows-specific | Status: not compiled on Linux; may be platform-gated Windows-only. Audit needed on Windows before declaring removable. |

## New Removal Candidates (zero native/codegen callers, interpreter duplicate exists)

| C File | Symbols | Status | Blocker |
|--------|---------|--------|---------|
| `runtime_base64.c` | `__c_rt_base64_encode`, `__c_rt_base64_decode` | **Already deleted** — confirmed GONE from disk 2026-05-29. Moved to Removed table. | — |

Verification for the 2026-05-27 runtime hash/crypto removal:

```bash
cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::utils --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::crypto_compare --manifest-path src/compiler_rust/Cargo.toml
bin/simple check src/compiler_rust/lib/std/src/infra/hash.spl src/lib/nogc_sync_mut/src/hash.spl
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

**2026-05-29 build-input audit correction:** Prior entries for runtime_math/random/contracts/error/equality/value/format/config/env/regex_stub claimed "the core-C runtime bundle still compiles it." This was **incorrect** — verified 2026-05-29 that none of these files appear in `runtime/build.rs` c_sources OR `tools.rs` runtime_inputs. `runtime_math.c`, `runtime_random.c`, `runtime_error.c`, `runtime_config.c`, `runtime_contracts.c`, `runtime_regex_stub.c`, `runtime_equality.c`, `runtime_format.c`, `runtime_value.c`, and `runtime_env.c` were deleted after their Rust replacements were exported with stable ABI symbols or no legacy helper callers remained.

Additional 2026-05-27 simple-runtime reductions:

- `value/sffi/math.rs` now implements and exports the `rt_math_*` wrappers
  directly in Rust using standard `f64` operations and a Rust `gcd`, so
  `runtime_math.c` was deleted.
- `value/sffi/random.rs` now implements and exports the legacy LCG state and
  random-hex helper directly in Rust, so `runtime_random.c` was deleted.
- `value/sffi/config.rs` now implements and exports the macro-trace and
  debug-mode flags as Rust `AtomicBool` state, so `runtime_config.c` was
  deleted.
- `value/sffi/error_handling.rs` now emits the not-found diagnostics and
  returns the Rust runtime error sentinel directly via exported ABI symbols, so
  `runtime_error.c` was deleted.
- `value/sffi/value_ops.rs` and the pointer conversion helpers in
  `value/sffi/memory.rs` now implement and export the value helpers directly
  in Rust, so `runtime_value.c` was deleted. `runtime_value.h` stays as the C
  ABI header for remaining C runtime sources.
- `value/sffi/equality.rs` now implements and exports value/native equality
  and comparison directly in Rust, so `runtime_equality.c` was deleted.
- The stale `runtime_ctype.c` entry was removed from `runtime/build.rs`; that
  C source was already deleted and skipped by the build when absent.
- `value/sffi/contracts.rs` now implements and exports the contract diagnostics
  and abort behavior directly in Rust, so `runtime_contracts.c` was deleted.
- `value/sffi/regex_stub.rs` now implements and exports the disabled-regex
  stub behavior directly in Rust, so `runtime_regex_stub.c` was deleted.
- `value/sffi/io_print.rs` now implements and exports value formatting, raw u64
  stringification, and display-string conversion directly in Rust, so
  `runtime_format.c` was deleted.
- `value/sffi/env_process.rs` and `value/sffi/io_print.rs` now implement and
  export env/platform/process/terminal and flush helpers directly in Rust, so
  `runtime_env.c` was deleted.
- `value/pty.rs` now exports `rt_pty_open` and `rt_pty_spawn` directly in
  Rust, so `runtime/build.rs` no longer compiles `runtime_pty.c`.

Verification:

```bash
cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::math --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::random --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::config --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::error_handling --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime value::tests::test_sffi_functions --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::equality --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::contracts --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::regex_stub --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::io_print --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime value::pty --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::env_process --manifest-path src/compiler_rust/Cargo.toml
```

## Path to C Removal for Remaining Modules

**Verified build inputs (2026-05-29):** The core-C runtime bundle compiles exactly the files listed in `runtime/build.rs` c_sources and `tools.rs` runtime_inputs. No glob sweep; no amalgamation. Files absent from both lists are only kept if codegen/SFFI dispatch resolves their symbols at link time.

For **math/random/config/error**:
Deleted 2026-05-29. Their Rust replacements now use exported C ABI symbols
where a stable native symbol is required. The core-C tiny-native bundle did not
compile these files; `runtime_native.c` retains the tiny-native
`rt_function_not_found` implementation it already owned.

For **equality/value/format/env** (Group A2 — SFFI dispatch table):
Deleted 2026-05-29. Former `rt_value_*`, `rt_env_*`, `rt_value_eq`, and
`rt_value_format_string` SFFI blockers now resolve to Rust-exported symbols, or
the exact legacy `__c_rt_*` helpers had no active callers.

For **contracts/regex_stub**:
Deleted 2026-05-29. `simple_contract_check*` and `sffi_regex_*` are still
referenced by codegen dispatch, but both the always-on contract module and the
disabled-regex stub module now export the required symbols from Rust. The
`runtime-regex` feature path already exported the real regex implementation.

For **runtime_pty.c**:
Deleted 2026-05-29. Zero build references were reconfirmed before deletion:
not in `runtime/build.rs` c_sources, not in `native_project/tools.rs`
runtime_inputs, and no other build.rs references it. `value/pty.rs` exports
`rt_pty_open` and `rt_pty_spawn` via `#[no_mangle]`; the `-lutil` link in
`runtime/build.rs` is for the Rust `openpty(3)` call inside `value/pty.rs`.
The `interpreter_extern/pty.rs` handles interpreter mode independently, and the
std PTY comments now point at the Rust implementations.

For **memory/time** (`runtime/build.rs` c_sources):
Compiled directly into `libruntime_sffi_c.a`. `runtime_memory.c` is core ABI (codegen emits `rt_alloc` for every alloc). `runtime_time.c` wraps `clock_gettime`/`gettimeofday` — must stay native. Pure Simple `time_utils.spl` provides civil-date arithmetic on top.

For **native/legacy_core/mcp_core/simd_utf8** (`tools.rs` runtime_inputs):
Compiled into the core-C runtime library for native builds. `runtime_native.c` is the foundation of the runtime ABI. `runtime_legacy_core.c` is a minimal bridge shim. Cannot remove without restructuring the ABI layer.

For **string_index/async_driver**:
Referenced via the codegen SFFI dispatch table and interpreter extern. Removal requires the native-build linker to resolve them from Simple-compiled objects instead of the C archive. Blocked by the cross-module ABI bug. Note: `runtime_string_index.c` and `async_driver.c` do NOT appear in the confirmed build inputs — they may only be linked via SFFI table references. A focused linker audit is needed.

For **audio/font/fork/image/memtrack/process/sdl2/simd/thread/scv_wasm/regex**:
SPL extern declarations still point at C symbols. Removal requires either a
pure-Simple replacement exporting the same symbol name, or updating all `extern fn`
declarations to point at a new Rust export.

For **runtime.c** (bootstrap): needed for stage0/stage1 bootstrap only. Can be
excluded from the self-hosted build once `--bootstrap-exclude-legacy-runtime` flag
is wired into the build system.

For **runtime_db.c**: Active SQLite wrapper; multiple spl callers. Compiled by `runtime/build.rs`. Cannot remove without a pure-Simple or Rust SQLite replacement wired through the same symbols.

For **hosted_cocoa.c / hosted_win32.c**: Zero Linux build references confirmed. Status on macOS/Windows is unknown — audit on those platforms before declaring removable or keeping.

## Pure Simple Replacements (coexist with C)

These serve Simple code via `use std.common.X`. They do NOT replace the C
symbols — they provide equivalent functionality at the stdlib layer.

| Module | File | Tests |
|--------|------|-------|
| ctype | `src/lib/common/ctype.spl` | 9/9 |
| math | `src/lib/common/math/math.spl` | 13/13 |
| error | `src/lib/common/error/error.spl` | 4/4 |
| contracts | `src/lib/common/contracts/contracts.spl` | 8/8 |
| random | `src/lib/common/random_pure.spl` | 21/21 |
| time_utils | `src/lib/common/time_utils.spl` | 53/53 |
| audio_effects | `src/lib/common/audio_effects.spl` | 7/7 |
