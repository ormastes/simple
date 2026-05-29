# C Runtime Exclusion Analysis

**Date:** 2026-05-18
**Last audited:** 2026-05-29 (follow-up pass — pty blocker cleared, A2 blockers reconfirmed, no new C files)
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

These files exist on disk, `simple-runtime` no longer compiles them, and they do NOT appear in any `build.rs` `c_sources[]` or `tools.rs` `runtime_inputs[]` list (verified 2026-05-29). They remain only if codegen or the SFFI dispatch table still resolves their symbols at link time. A follow-up codegen/linker audit is needed before deletion.

Verified blocker categories (2026-05-29, confirmed unchanged in follow-up pass):
- **SFFI dispatch table** (`codegen/runtime_sffi.rs`): `rt_value_*`, `rt_env_*`, `rt_value_format_string`, `rt_value_eq`, `rt_value_compare`, `rt_native_eq` confirmed still present → those files cannot be deleted until the SFFI table routes to Rust exports.
- **`calls.rs` codegen dispatch**: `simple_contract_check`, `simple_contract_check_msg`, `sffi_regex_*` (8 variants) confirmed still present → contracts/regex_stub blocked.
- **Interpreter extern Rust FFI** (`interpreter_extern/math.rs`): `rt_math_*` symbols are resolved from the Rust `simple-runtime` crate directly — NOT from the C file. Same for pty (now confirmed: pty C file not in any build input).
- **Core-C tiny-native lane** (`build_core_c_runtime_library` in `native_project/tools.rs`): confirmed runtime_inputs = `[runtime_native.c, runtime_legacy_core.c, runtime_mcp_core.c, runtime_simd_utf8.c]` plus optional `runtime_https_openssl_core.c`. Does NOT include pty, math, random, error, config. This lane does NOT link the Rust `simple-runtime` crate. Remaining gate for math/random/error/config.
- **No new C files** since 2026-05-29 first pass — 36 C files on disk, exactly matching the prior audit.

| C File | Key Symbols | Rust Replacement | .spl Callers | Confirmed Blocker |
|--------|-------------|-----------------|-------------|---------|
| `runtime_math.c` | 27 (`rt_math_*`) | `value/sffi/math.rs`; interpreter via `interpreter_extern/math.rs` | 12 files | **Core-C tiny-native lane only** — interpreter and `simple-runtime` already use Rust; tiny-native build does not link Rust crate so these symbols would be unresolved. Not in SFFI dispatch table. |
| `runtime_random.c` | 8 (`rt_random_*`) | `value/sffi/random.rs` | 10 files | Same as math — core-C tiny-native lane gap. Not in SFFI dispatch table. |
| `runtime_contracts.c` | 2 (`simple_contract_check*`) | `value/sffi/contracts.rs` | 3 files | `calls.rs` codegen dispatch confirmed (`simple_contract_check`, `simple_contract_check_msg`). |
| `runtime_error.c` | `rt_function_not_found`, `rt_method_not_found` | `value/sffi/error_handling.rs` | 2 files | Core-C tiny-native lane gap (not in SFFI dispatch or calls.rs). Verify Rust export `#[export_name]` is visible to native link. |
| `runtime_equality.c` | `rt_native_eq`, `rt_native_neq`, `rt_value_eq`, `rt_value_compare` | `value/sffi/equality.rs` | 0 direct | `rt_value_eq`/`rt_value_compare` confirmed in SFFI dispatch table (`runtime_sffi.rs`). |
| `runtime_value.c` | `rt_value_int/float/bool/nil`, `rt_value_as_int`, `rt_value_truthy`, `rt_value_is_nil/int/float/bool/heap`, `rt_value_type_tag` | `value/sffi/value_ops.rs`, `value/sffi/memory.rs` | 0 direct | `rt_value_int/float/bool/nil/as_int/truthy/to_ptr` confirmed in SFFI dispatch table. `runtime_value.h` header must stay even if `.c` is removed. |
| `runtime_format.c` | `__c_rt_value_format_string`, `__c_rt_raw_u64_to_str`, `__c_rt_value_to_display_str` | `value/sffi/io_print.rs` | 0 direct | `rt_value_format_string` confirmed in SFFI dispatch table. |
| `runtime_config.c` | `rt_set_macro_trace`, `rt_is_macro_trace_enabled`, `rt_set_debug_mode`, `rt_is_debug_mode_enabled` | `value/sffi/config.rs` (AtomicBool) | 0 direct | Core-C tiny-native lane gap (not confirmed in SFFI dispatch or calls.rs). |
| `runtime_env.c` | `__c_rt_env_get_i64`, `__c_rt_env_set/exists/remove/get_str/cwd/home/temp`, `__c_rt_exit`, `__c_rt_stdout/stderr_flush`, `__c_rt_platform_name`, `__c_rt_term_get_size` | `value/sffi/env_process.rs`, `value/sffi/io_print.rs` | 0 direct | `rt_env_get/set/exists/remove/cwd/home/temp/get_i64` confirmed in SFFI dispatch table. `calls.rs` also references `rt_env_get*`. |
| `runtime_regex_stub.c` | `sffi_regex_is_match/find/find_all/captures/replace/replace_all/split/split_n` | `value/sffi/regex_stub.rs` | `nogc_sync_mut/io/regex_simple.spl` | `sffi_regex_*` confirmed in `calls.rs` codegen dispatch. |
<<<<<<< Conflict 1 of 3
+++++++ Contents of side #1
| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | `value/pty.rs` (runtime `#[no_mangle]`), `interpreter_extern/pty.rs` (interp) | `sys/pty.spl`, `smux/smux_remote.spl` | **Blocker cleared** (follow-up 2026-05-29). Zero build refs confirmed. `value/pty.rs` line 121/135: `#[no_mangle] pub extern "C" fn rt_pty_open/rt_pty_spawn` — both symbols exported from Rust. `runtime/build.rs` `-lutil` linkage is for the Rust `openpty` call, not the C file. Not in SFFI dispatch or calls.rs. Move to "Safe to delete" candidates. Also: `pty.spl` line 5 comment and `interpreter_extern/pty.rs` doc-comment are stale — both still claim compiled mode uses `runtime_pty.c`. |
%%%%%%% Changes from base to side #2
-| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | `value/pty.rs` (runtime), `interpreter_extern/pty.rs` (interp) | `sys/pty.spl`, `smux/smux_remote.spl` | Zero build.rs/tools.rs refs (confirmed 2026-05-29). Not in SFFI dispatch table. Core-C tiny-native lane gap — `build_core_c_runtime_library` does not include pty.c but tiny-native programs that use PTY would need the C symbols unless the Rust export is visible. |
+| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | `value/pty.rs` (runtime), `interpreter_extern/pty.rs` (interp) | `sys/pty.spl`, `smux/smux_remote.spl` | **Blocker cleared (2026-05-29).** Zero refs in `build.rs` c_sources and `tools.rs` runtime_inputs. Not in SFFI dispatch table. Rust `value/pty.rs` exports both symbols via `#[no_mangle]`. Safe to delete — see "New Removal Candidates" section. |
>>>>>>> Conflict 1 of 3 ends

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
<<<<<<< Conflict 2 of 3
+++++++ Contents of side #1
| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | **Safe to delete** — zero refs in all `build.rs`/`tools.rs` confirmed. `value/pty.rs` exports both symbols via `#[no_mangle]`; `runtime/build.rs` links `-lutil` for the *Rust* `openpty` call, not the C file. No native build path compiles this C file. `interpreter_extern/pty.rs` provides the interpreter path independently. Stale comments in `pty.spl` (line 5: "implemented in runtime_pty.c") and `interpreter_extern/pty.rs` (doc comment claims compiled mode uses C) need updating after deletion. | — (blocker cleared 2026-05-29 follow-up) |
%%%%%%% Changes from base to side #2
-| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | **Removable (pending verification)** — zero refs in all `build.rs`/`tools.rs` as of 2026-05-29; Rust replacements export the same symbols. | Confirm no native binary links the C object before deleting. |
+| `runtime_pty.c` | `rt_pty_open`, `rt_pty_spawn` | **Safe to delete** — zero refs in `build.rs` c_sources and `tools.rs` runtime_inputs (confirmed 2026-05-29). Not in SFFI dispatch table. Rust `value/pty.rs` exports both `rt_pty_open` and `rt_pty_spawn` via `#[no_mangle]`; interpreter path is `interpreter_extern/pty.rs`. No remaining build path pulls the C object. | None — blocker cleared. |
>>>>>>> Conflict 2 of 3 ends
| `runtime_base64.c` | `__c_rt_base64_encode`, `__c_rt_base64_decode` | **Already deleted** — confirmed GONE from disk 2026-05-29. Moved to Removed table. | — |

Verification for the 2026-05-27 runtime hash/crypto removal:

```bash
cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::utils --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::crypto_compare --manifest-path src/compiler_rust/Cargo.toml
bin/simple check src/compiler_rust/lib/std/src/infra/hash.spl src/lib/nogc_sync_mut/src/hash.spl
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

**2026-05-29 build-input audit correction:** Prior entries for runtime_math/random/contracts/error/equality/value/format/config/env/regex_stub claimed "the core-C runtime bundle still compiles it." This was **incorrect** — verified 2026-05-29 that none of these files appear in `runtime/build.rs` c_sources OR `tools.rs` runtime_inputs. The actual blockers differ per file: SFFI dispatch table (`rt_value_*`, `rt_env_*`), `calls.rs` codegen dispatch (`simple_contract_check*`, `sffi_regex_*`), or the core-C tiny-native lane gap (math/random/error/config — interpreter already uses Rust, tiny-native build does not link Rust crate). They are reclassified to Group A2.

Additional 2026-05-27 simple-runtime reductions:

- `value/sffi/math.rs` now implements the `rt_math_*` wrappers directly in
  Rust using standard `f64` operations and a Rust `gcd`, so
  `runtime/build.rs` no longer compiles `runtime_math.c`.
- `value/sffi/random.rs` now implements the legacy LCG state and random-hex
  helper directly in Rust, so `runtime/build.rs` no longer compiles
  `runtime_random.c`.
- `value/sffi/config.rs` now implements the macro-trace and debug-mode flags as
  Rust `AtomicBool` state, so `runtime/build.rs` no longer compiles
  `runtime_config.c`.
- `value/sffi/error_handling.rs` now emits the not-found diagnostics and
  returns the Rust runtime error sentinel directly, so `runtime/build.rs` no
  longer compiles `runtime_error.c`.
- `value/sffi/value_ops.rs` and the pointer conversion helpers in
  `value/sffi/memory.rs` now implement the value helpers directly in Rust, so
  `runtime/build.rs` no longer compiles `runtime_value.c`.
- `value/sffi/equality.rs` now implements value/native equality and comparison
  directly in Rust, so `runtime/build.rs` no longer compiles
  `runtime_equality.c`.
- The stale `runtime_ctype.c` entry was removed from `runtime/build.rs`; that
  C source was already deleted and skipped by the build when absent.
- `value/sffi/contracts.rs` now implements the contract diagnostics and abort
  behavior directly in Rust, so `runtime/build.rs` no longer compiles
  `runtime_contracts.c`.
- `value/sffi/regex_stub.rs` now implements the disabled-regex stub behavior
  directly in Rust, so `runtime/build.rs` no longer compiles
  `runtime_regex_stub.c`.
- `value/sffi/io_print.rs` now implements value formatting, raw u64
  stringification, and display-string conversion directly in Rust, so
  `runtime/build.rs` no longer compiles `runtime_format.c`.
- `value/pty.rs` now exports `rt_pty_open` and `rt_pty_spawn` directly in
  Rust, so `runtime/build.rs` no longer compiles `runtime_pty.c`.
- `value/sffi/env_process.rs` and `value/sffi/io_print.rs` now implement
  env/platform/terminal helpers, process exit, and stdout/stderr flush directly
  in Rust, so `runtime/build.rs` no longer compiles `runtime_env.c`.

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

For **math/random/config/error** (Group A2 — core-C tiny-native lane gap):
Not in any build.rs or tools.rs compile list. `simple-runtime` and the interpreter resolve these from Rust. The remaining gate is the **core-C tiny-native lane** (`build_core_c_runtime_library`), which does NOT link the Rust crate. For any native binary using these symbols, the Rust `#[export_name]` exports must be visible to the link step. Removal requires confirming the tiny-native lane can find these symbols through the native archive or a Rust-compiled object.

For **equality/value/format/env** (Group A2 — SFFI dispatch table):
Symbols confirmed in `codegen/runtime_sffi.rs` dispatch table (`rt_value_*`, `rt_env_*`, `rt_value_eq`, `rt_value_format_string`). Removal requires the SFFI table to resolve these from Rust exports (`#[export_name]`) rather than a C object. Pending SFFI audit.

For **contracts/regex_stub** (Group A2 — calls.rs codegen dispatch):
`simple_contract_check*` and `sffi_regex_*` confirmed in `codegen/instr/calls.rs`. Removal requires confirming the Rust `#[export_name]` implementations satisfy the codegen link step.

For **runtime_pty.c**:
<<<<<<< Conflict 3 of 3
+++++++ Contents of side #1
**Safe to delete** (confirmed follow-up 2026-05-29). Zero build references — not in `runtime/build.rs` c_sources, not in `native_project/tools.rs` runtime_inputs, no other build.rs references it. `value/pty.rs` exports `rt_pty_open` and `rt_pty_spawn` via `#[no_mangle]`; the `-lutil` link in `runtime/build.rs` is for the Rust `openpty(3)` call inside `value/pty.rs`. The `interpreter_extern/pty.rs` handles interpreter mode independently. After deletion: update stale comment in `src/compiler_rust/lib/std/src/sys/pty.spl` (line 5) and doc-comment in `src/compiler_rust/compiler/src/interpreter_extern/pty.rs` (says "compiled/native path uses the C symbols").
%%%%%%% Changes from base to side #2
-Zero build references confirmed 2026-05-29. Rust replacements (`value/pty.rs`, `interpreter_extern/pty.rs`) export the same C symbols. Pending: confirm no native binary link step pulls the C object. Likely safe to delete.
+**Blocker cleared (2026-05-29).** Zero build references in `build.rs` c_sources and `tools.rs` runtime_inputs. Not in SFFI dispatch table. Rust `value/pty.rs` provides both `rt_pty_open` and `rt_pty_spawn` via `#[no_mangle]`; interpreter path is `interpreter_extern/pty.rs`. Safe to delete.
>>>>>>> Conflict 3 of 3 ends

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
