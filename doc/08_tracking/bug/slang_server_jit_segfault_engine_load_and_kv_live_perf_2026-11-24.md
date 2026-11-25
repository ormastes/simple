# slang server segfaults in engine_ensure_loaded under seed JIT; kv_cache_live exact_repeat not faster on 15M model

Found by the llmkv sweep, 2026-11-24, seed `C:/dev/seeds/simple-release.exe`, Windows, Vulkan shim rebuilt from release tip.

## 1. `simple run` (default JIT) segfaults loading any model (rc 139 / 0xC0000005)
- `simple run src/app/slang_server/main.spl -- --plaintext-development --models=<root> --model=gemma-3-270m-it-GGUF` dies in `engine_preload` -> `engine_ensure_loaded` (banner prints, never "resident:").
- Reproduced with a 6-line probe calling `engine_ensure_loaded(m)`; shim-independent (old Vulkan shim, CPU mm shim, SLANG_GPU on or off).
- `SIMPLE_EXECUTION_MODE=interpret` loads fine and the server listens (verified by hand). In-spec loads under `simple test` (interpreter) pass.
- Effect: `slang_http_server_live_spec`, `slang_openai_conformance_live_spec` (13/14 fail, "connect failed"), `caret_slang_local_hello_system_spec` (child exit -1073741819) fail because the spec spawns the server with the default JIT mode.
- With `SIMPLE_EXECUTION_MODE=interpret` exported for the spec run, `process_spawn_redirected` returns -1 ("could not start slang_server child (pid -1)"), so the spec cannot be driven that way either. Not yet root-caused (`host_is_windows_host()` / `windows_redirected_spawn` under the interpreter is the lead).
- Seed limitation, same class as `seed_http_server_handle_connection_dispatch_2026-09-04.md`; not a release-tip lib regression. Needs a seed JIT fix or the pure-Simple binary.

## 2. `slang_kv_cache_live_spec` fails on perf assertion — FIXED (2026-11-25)
- Root cause: in snapshot prefix-cache mode (mode 0), `slang_ggml_request_create` allocated a fresh `llama_context` (`warm = 0`) and `slang_request_close_locked` freed it on every request. Because `warm == 0`, `slang_request_first_ubatch` held back `n_ubatch` (512) tokens on every hit, so `exact_repeat` threw away 511 of 1041 cached prefix tokens (`prompt_tokens_on = 512`) and paid fresh context allocation + 512-token re-prefill (`on = 187 ms` vs `off = 35 ms`).
- Fix: `src/runtime/slang_ggml_shim.c` keeps a 1-slot warm idle `llama_context` pool (`g_idle_ctx`) for serial non-tree default-model requests, parked on request close after `llama_memory_clear` and dropped on `slang_free_locked`, `slang_ggml_context_profile_configure`, or `slang_ggml_prefix_cache_mode_configure`. Concurrent requests still allocate fresh contexts (`warm = 0`) and keep the `n_ubatch` warmup backoff.
- Verification (2026-11-25):
  - C contract tests: `prefix_cache_test.c` (verifies both concurrent fresh-context backoff and serial warm-context full prefix reuse) + `tree_cache_test.c` — both `STATUS: PASS`.
  - Live Vulkan `test/03_system/lib/slang/feature/slang_kv_cache_live_spec.spl` (`llama2c-stories15M-GGUF`, `n_ctx=2048`): `exact_repeat` `off=24 ms` vs `on=15 ms` (`1.60x` speedup), `prompt_tokens_on=1` (down from 512), `first_diff_byte=-1` on all 4 workloads, `1/1 PASS`. Note: `cold` (`165 ms`) and `prefix_extension` (`968 ms`) still pay Vulkan snapshot readback on cache admission, which is expected on a tiny 15M model.

## 3. Not a bug: `SLANG_RUNNER` must be `pure` or `ggml`; the first sweep failures with `SLANG_RUNNER=1` were operator error.

## Passing on the tip (Vulkan, seed): kv_cache_live_exact_output (Qwen), kv_tree_cache_live 4/4, paged_kv_backend, gpu_offload_live, model_variety_live 7/7, caret_local_usage, local_model_root_hello 2/2.
