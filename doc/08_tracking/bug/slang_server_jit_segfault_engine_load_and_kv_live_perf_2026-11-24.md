# slang server segfaults in engine_ensure_loaded under seed JIT; kv_cache_live exact_repeat not faster on 15M model

Found by the llmkv sweep, 2026-11-24, seed `C:/dev/seeds/simple-release.exe`, Windows, Vulkan shim rebuilt from release tip.

## 1. `simple run` (default JIT) segfaults loading any model (rc 139 / 0xC0000005) — FIXED (2026-11-25)
- Original failure: `simple run src/app/slang_server/main.spl -- --plaintext-development --models=<root> --model=gemma-3-270m-it-GGUF` died in `engine_preload` -> `engine_ensure_loaded` -> `host_free_ram_bytes` -> `process_run_bounded_bytes` -> `rt_process_run_bounded_bytes` with `0xC0000005` (`rip = 0x0`).
- Root cause (two parts):
  1. `rt_process_run_bounded_bytes` was missing from `RUNTIME_SYMBOL_NAMES` (`src/compiler_rust/common/src/runtime_symbols.rs`), so `seed_jit_runtime_symbol_table` (`jit.rs`) never registered it with `JITBuilder`.
  2. `jit_import_resolves` (`src/compiler_rust/compiler/src/codegen/jit.rs`) checked `elf_utils::resolve_runtime_symbol(name)` without verifying `RUNTIME_SYMBOL_NAMES.contains(&name)`. Because `elf_utils.rs` listed `rt_process_run_bounded_bytes`, `jit_import_resolves` returned `true`, bypassing both `exec_core`'s interpreter bridge and `unresolved_imports_called` so Cranelift finalized a NULL GOT slot and jumped to `0x0`.
- Fix:
  - Added `"rt_process_run_bounded_bytes"` to `RUNTIME_SYMBOL_NAMES` and re-exported `rt_process_run_bounded_bytes` from `simple_runtime::value`.
  - Aligned `jit_import_resolves` with `seed_jit_runtime_symbol_table` so `provider`/`elf_utils` matches only count when `RUNTIME_SYMBOL_NAMES.contains(&name)`.
  - Added JIT unit tests (`test_jit_import_resolves_agrees_with_seed_symbol_table_and_registers_bounded_bytes`, `test_jit_calls_rt_process_run_bounded_bytes_without_null_jump`).
- Companion `SIMPLE_EXECUTION_MODE=interpret` spawn failure (`process_spawn_redirected` returning `-1` on stale `.scope` dirs) was fixed separately in PR #11381.
- Verification (2026-11-25): `cargo test --release -p simple-compiler --lib -- codegen::jit::tests` (32/32 PASS), `runtime_symbol_registration_gate` (PASS), and `engine_preload("C:/dev/keep/model", "gemma-3-270m-it-GGUF")` under default JIT (old seed: rc `139`; rebuilt seed: rc `0`, `ENGINE_LOAD_OK=()`). Note: takes effect for `simple run` once the host seed is refreshed with this commit.

## 2. `slang_kv_cache_live_spec` fails on perf assertion — FIXED (2026-11-25)
- Root cause: in snapshot prefix-cache mode (mode 0), `slang_ggml_request_create` allocated a fresh `llama_context` (`warm = 0`) and `slang_request_close_locked` freed it on every request. Because `warm == 0`, `slang_request_first_ubatch` held back `n_ubatch` (512) tokens on every hit, so `exact_repeat` threw away 511 of 1041 cached prefix tokens (`prompt_tokens_on = 512`) and paid fresh context allocation + 512-token re-prefill (`on = 187 ms` vs `off = 35 ms`).
- Fix: `src/runtime/slang_ggml_shim.c` keeps a 1-slot warm idle `llama_context` pool (`g_idle_ctx`) for serial non-tree default-model requests, parked on request close after `llama_memory_clear` and dropped on `slang_free_locked`, `slang_ggml_context_profile_configure`, or `slang_ggml_prefix_cache_mode_configure`. Concurrent requests still allocate fresh contexts (`warm = 0`) and keep the `n_ubatch` warmup backoff.
- Verification (2026-11-25):
  - C contract tests: `prefix_cache_test.c` (verifies both concurrent fresh-context backoff and serial warm-context full prefix reuse) + `tree_cache_test.c` — both `STATUS: PASS`.
  - Live Vulkan `test/03_system/lib/slang/feature/slang_kv_cache_live_spec.spl` (`llama2c-stories15M-GGUF`, `n_ctx=2048`): `exact_repeat` `off=24 ms` vs `on=15 ms` (`1.60x` speedup), `prompt_tokens_on=1` (down from 512), `first_diff_byte=-1` on all 4 workloads, `1/1 PASS`. Note: `cold` (`165 ms`) and `prefix_extension` (`968 ms`) still pay Vulkan snapshot readback on cache admission, which is expected on a tiny 15M model.

## 3. Not a bug: `SLANG_RUNNER` must be `pure` or `ggml`; the first sweep failures with `SLANG_RUNNER=1` were operator error.

## Passing on the tip (Vulkan, seed): kv_cache_live_exact_output (Qwen), kv_tree_cache_live 4/4, paged_kv_backend, gpu_offload_live, model_variety_live 7/7, caret_local_usage, local_model_root_hello 2/2.
