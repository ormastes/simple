# C Runtime Exclusion Analysis

**Date:** 2026-05-18
**Status:** Open — audit still tracks removable C runtime candidates and blocked removals.
**Context:** Pure Simple conversion project — which C files can be removed

## Removed (zero callers)

| C File | Symbols | Action |
|--------|---------|--------|
| `runtime_ctype.c` | `__is_alnum/alpha/digit/xdigit/space/lower/upper` | Deleted. Rust shim had zero pub fns. Removed from tools.rs. |
| `runtime_audio_effects.c` | `rt_audio_set_pitch` + 6 stubs | Deleted. Not in tools.rs. Zero .rs/.spl callers. |
| `runtime_hash.c` | `rt_fnv_hash` | Deleted 2026-05-27. `simple-runtime` now implements FNV-1a in Rust and the legacy Rust std hash shim computes FNV in Simple instead of declaring the C extern. Removed from the core-C native-project runtime input list. |
| `runtime_crypto.c` | `rt_constant_time_compare` | Deleted 2026-05-27. `simple-runtime` and interpreter dispatch both implement constant-time comparison in Rust/Simple runtime code; no native-project runtime input remains. |

## Cannot Remove (active Rust/codegen callers)

### Group A — Codegen hard deps (blocked by cross-module ABI)

Symbols emitted directly by codegen or referenced in `elf_utils.rs`/`runtime_sffi.rs`.
Cannot remove until native linker resolves them from Simple-compiled objects.

| C File | Key Symbols | Codegen Callers | .spl Callers | Why It Stays |
|--------|-------------|-----------------|-------------|-------------|
| `runtime_math.c` | 27 (`rt_math_*`) | codegen/core-C native-project archive | 12 files | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native SFFI exports. |
| `runtime_random.c` | 8 (`rt_random_*`) | codegen/core-C native-project archive | 10 files | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native SFFI exports. |
| `runtime_contracts.c` | 2 (`simple_contract_check*`) | codegen/core-C native-project archive | 3 files | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native contract-check exports. |
| `runtime_error.c` | `rt_function_not_found`, `rt_method_not_found` | codegen/core-C native-project archive | 2 files | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native unresolved-call fallbacks. |
| `runtime_time.c` | 18 (`rt_time_*`, `rt_timestamp_*`) | 8+ files | **199 files** | Most used runtime module; syscall wrappers |
| `runtime_equality.c` | `rt_native_eq`, `rt_native_neq`, `rt_value_eq`, `rt_value_compare` | codegen/core-C native-project archive | 0 direct | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native equality exports. |
| `runtime_memory.c` | `rt_alloc`, `rt_free`, `rt_ptr_read_i64/i32`, `rt_ptr_write_*`, `rt_memset`, `rt_memcpy` | `codegen/instr/core.rs`, `memory.rs`, `closures_structs.rs`, `llvm/objects.rs` | gpu/memory.spl, ptr/raw.spl, torch/sffi.spl, sffi/llvm_loader.spl | Codegen emits `rt_alloc` for every struct/array alloc; core ABI |
| `runtime_value.c` | `rt_value_int/float/bool/nil`, `rt_value_as_int`, `rt_value_truthy`, `rt_value_is_nil/int/float/bool/heap`, `rt_value_type_tag` | none in `simple-runtime` as of 2026-05-27 | 0 direct | Rust runtime crate now implements value operations and pointer conversions directly; core C/native runtime still keeps this source for native value helpers |
| `runtime_format.c` | `__c_rt_value_format_string` (→ `rt_value_format_string`), `__c_rt_raw_u64_to_str`, `__c_rt_value_to_display_str` | codegen/core-C native-project archive | 0 direct | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native formatting exports. |
| `runtime_native.c` | `rt_print`, `rt_println`, `rt_stdout_write`, `rt_stderr_write`, `rt_stdin_read_line`, `rt_string_new/len/data`, `rt_native_eq`, `rt_interp_call`, `rt_to_string`, etc. | `codegen/instr/calls.rs`, `linker/stubs.rs`, `elf_utils.rs`, interpreter dispatch | 0 direct (exposed via `use std.*`) | Foundation of the runtime ABI — strings, I/O, value boxing |
| `runtime_string_index.c` | `rt_swi_build/char_to_byte/byte_to_char/free`, `rt_rank_select_build`, `rt_rank_query`, `rt_select_query`, `rt_rank_select_free` | `codegen/runtime_sffi.rs` (8 entries), `interpreter_extern/simd.rs` | 0 direct | Codegen SFFI table + interpreter extern; Unicode index structures |
| `async_driver.c` | `rt_driver_create/destroy`, `rt_driver_submit_*` (13 variants), `rt_driver_poll*`, `rt_driver_cancel` | `codegen/runtime_sffi.rs` (15 entries), `codegen/instr/calls.rs`, `llvm/functions/calls.rs` | 0 direct spl; driven via codegen SFFI | Async I/O driver; codegen emits all submit/poll calls |
| `runtime_config.c` | `rt_set_macro_trace`, `rt_is_macro_trace_enabled`, `rt_set_debug_mode`, `rt_is_debug_mode_enabled` | codegen/core-C native-project archive | 0 direct | `simple-runtime` no longer calls the C file as of 2026-05-27; the core-C runtime bundle still compiles it for native SFFI exports. |
| `runtime_env.c` | `__c_rt_env_get_i64`, `__c_rt_env_set/exists/remove/get_str/cwd/home/temp`, `__c_rt_exit`, `__c_rt_stdout/stderr_flush`, `__c_rt_platform_name`, `__c_rt_term_get_size` | `codegen/runtime_sffi.rs` (`rt_env_*` family), `interpreter_extern/system.rs` | 0 direct (wrapped by Rust `rt_env_*` shims) | Env/platform syscall wrappers; Rust shims expose as `rt_env_*` |

### Group B — SPL FFI surface (blocked by no Simple replacement yet)

Symbols called from `.spl` extern declarations. Cannot remove until a pure-Simple
or Rust-only replacement is wired through the same symbol name.

| C File | Key Symbols | .rs Callers | .spl Callers | Why It Stays |
|--------|-------------|-------------|-------------|-------------|
| `runtime_audio.c` | `rt_audio_init/shutdown/load_sound/unload_sound/play/play_looped/stop/pause/resume/set_volume/set_master_volume/get_master_volume/is_playing` + spatial fns | 0 Rust codegen | `nogc_sync_mut/io/audio_sffi.spl` | miniaudio wrapper; spl audio layer |
| `runtime_base64.c` | `__c_rt_base64_encode`, `__c_rt_base64_decode` | `runtime/src/value/sffi/utils.rs` wraps both | `nogc_sync_mut/oidc/id_token.spl` (via `rt_base64url_decode`) | Used in SHA1/websocket handshake and OIDC |
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
| `runtime_regex_stub.c` | `sffi_regex_is_match/find/find_all/captures/replace/replace_all/split/split_n` | `codegen/instr/calls.rs` (dispatch table), `interpreter_extern/mod.rs` | `nogc_sync_mut/io/regex_simple.spl` | `simple-runtime` no longer calls the C file as of 2026-05-27; native codegen still links regex stub symbols when the full regex runtime is unavailable. |

## New Removal Candidates (zero native/codegen callers, interpreter duplicate exists)

| C File | Symbols | Status | Blocker |
|--------|---------|--------|---------|
| _none currently verified_ | — | The 2026-05-27 pass removed the two previously listed candidates. | Continue auditing Group A/B modules above. |

Verification for the 2026-05-27 runtime hash/crypto removal:

```bash
cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::utils --manifest-path src/compiler_rust/Cargo.toml
cargo test -p simple-runtime sffi::crypto_compare --manifest-path src/compiler_rust/Cargo.toml
bin/simple check src/compiler_rust/lib/std/src/infra/hash.spl src/lib/nogc_sync_mut/src/hash.spl
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
```

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
```

## Path to C Removal for Remaining Modules

For **math/random**: the Rust shim no longer calls these C files as of
2026-05-27. Remaining removal requires migrating the core-C/native-project
SFFI export path so native builds no longer need the archived C sources.

For **memory/native/string_index/async_driver/env**:
codegen-emitted or ABI-layer symbols. Removal requires the native-build linker to
resolve them from Simple-compiled objects instead of the C archive. Blocked by the
cross-module ABI bug.

For **time**: syscall wrappers (`clock_gettime`, `gettimeofday`). Must stay native.
The pure Simple `time_utils.spl` provides civil-date arithmetic on top.

For **audio/font/fork/image/memtrack/process/sdl2/simd/thread/scv_wasm/regex**:
SPL extern declarations still point at C symbols. Removal requires either a
pure-Simple replacement exporting the same symbol name, or updating all `extern fn`
declarations to point at a new Rust export.

For **runtime.c** (bootstrap): needed for stage0/stage1 bootstrap only. Can be
excluded from the self-hosted build once `--bootstrap-exclude-legacy-runtime` flag
is wired into the build system.

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
