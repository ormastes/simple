# slang server segfaults in engine_ensure_loaded under seed JIT; kv_cache_live exact_repeat not faster on 15M model

Found by the llmkv sweep, 2026-11-24, seed `C:/dev/seeds/simple-release.exe`, Windows, Vulkan shim rebuilt from release tip.

## 1. `simple run` (default JIT) segfaults loading any model (rc 139 / 0xC0000005)
- `simple run src/app/slang_server/main.spl -- --plaintext-development --models=<root> --model=gemma-3-270m-it-GGUF` dies in `engine_preload` -> `engine_ensure_loaded` (banner prints, never "resident:").
- Reproduced with a 6-line probe calling `engine_ensure_loaded(m)`; shim-independent (old Vulkan shim, CPU mm shim, SLANG_GPU on or off).
- `SIMPLE_EXECUTION_MODE=interpret` loads fine and the server listens (verified by hand). In-spec loads under `simple test` (interpreter) pass.
- Effect: `slang_http_server_live_spec`, `slang_openai_conformance_live_spec` (13/14 fail, "connect failed"), `caret_slang_local_hello_system_spec` (child exit -1073741819) fail because the spec spawns the server with the default JIT mode.
- With `SIMPLE_EXECUTION_MODE=interpret` exported for the spec run, `process_spawn_redirected` returns -1 ("could not start slang_server child (pid -1)"), so the spec cannot be driven that way either. Not yet root-caused (`host_is_windows_host()` / `windows_redirected_spawn` under the interpreter is the lead).
- Seed limitation, same class as `seed_http_server_handle_connection_dispatch_2026-09-04.md`; not a release-tip lib regression. Needs a seed JIT fix or the pure-Simple binary.

## 2. `slang_kv_cache_live_spec` fails on perf assertion
llama2c-stories15M (smallest runnable model): exact_repeat off 35 ms vs on 35 ms; assertion `on < off` fails. Cache-on cold/prefix_extension are 4-5x SLOWER than off (173/180 vs 40/38 ms) on the 15M model; prompt tokens do drop (1041 -> 512). Outputs byte-identical. Likely a per-request snapshot cost that dominates a tiny model; Qwen2.5-1.5B (exact_output spec) passes. Numbers: C:/dev/slang-logs/sweep/kv_perf.md.

## 3. Not a bug: `SLANG_RUNNER` must be `pure` or `ggml`; the first sweep failures with `SLANG_RUNNER=1` were operator error.

## Passing on the tip (Vulkan, seed): kv_cache_live_exact_output (Qwen), kv_tree_cache_live 4/4, paged_kv_backend, gpu_offload_live, model_variety_live 7/7, caret_local_usage, local_model_root_hello 2/2.
