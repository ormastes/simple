# Feature expert: slang local inference

**Feature:** running a local LLM through slang, and reaching it from caret.
**Last updated:** 2026-11-15

## The one-sentence shape

slang owns the model lifecycle, the memory admission, the residency decision
and the decode loop; ggml supplies the kernels (dequantization, attention,
tokenizer) that pure Simple does not have yet — the same division vLLM makes
when it drives cuBLAS/FlashAttention rather than writing GEMMs.

## Where the code lives

| Concern | File |
|---|---|
| Format detection (GGUF magic, safetensors header, slang pack) | `src/lib/gc_async_mut/slang/model_executor/model_loader/native_formats.spl` |
| Memory admission before a load | `src/lib/gc_async_mut/slang/model_executor/model_loader/memory_budget.spl` |
| Backend seam + slang's decode loop | `src/lib/gc_async_mut/slang/model_executor/backend.spl` |
| Resident model, load/swap policy | `src/lib/gc_async_mut/slang/engine/llm_engine.spl` |
| Offline (in-process) entrypoint | `src/lib/gc_async_mut/slang/entrypoints/llm.spl` |
| HTTP entrypoint | `src/lib/gc_async_mut/slang/entrypoints/openai/` |
| int64-only C boundary to ggml | `src/runtime/slang_ggml_shim.c` |
| Backend build | `scripts/check/build-slang-ggml-shim.shs` |
| Evidence gate (drives caret) | `scripts/check/check-slang-ggml-inference.shs` |

Caret side: providers `slang` (HTTP) and `slang_local` (in-process) in
`src/app/llm_caret/provider.spl`; model root config in `config.spl`
(`SLANG_MODEL_ROOT`).
`slang_local` sends the conversation as chat frames (`slang_generate_chat`, the model's own chat template, stops at its end-of-turn token); the old raw transcript made the model role-play "Assistant:" turns to the token cap. Admission overhead is `estimate_runtime_overhead_bytes(model_bytes, ENGINE_N_CTX)` (`memory_budget.spl`; KV = n_ctx * clamp(model_bytes/32768, 16..512 KiB) + 512 MiB), ~0.6 GiB for a 1.5B Q4 model at 4096 ctx.

## Things that will bite you

- **The seam is drawn at the decode loop, on purpose.** `generate` in
  `backend.spl` steps one token at a time so KV positions, stop conditions and
  the token budget stay in Simple. If you move the loop into C to make it
  faster, slang stops owning the thing that makes it slang.
- **Clear the KV cache between requests.** The model stays resident; the
  conversation must not. Each request gets its own context, and
  `slang_ggml_request_prefix_prepare` either clears it or restores only an
  exact-token prefix snapshot. Without
  it the second request answers while still attending to the first, then
  overruns `n_ctx`. Verified by generating twice in one process and getting
  independent answers.
- **Never read a shard whole.** Detection uses `file_read_text_at` for 4 bytes
  (GGUF magic) and 1 byte (safetensors header). These files are 12 GB each.
- **Memory is unified on this class of host** (DGX Spark GB10: 128 GB shared
  between CPU and GPU). An over-budget load does not swap, it takes the host
  down. `check_fit` runs before every load and refuses; do not add a bypass.
- **Recognised and runnable are different claims** and are separate fields.
  A safetensors model is recognised, sized and listed, and is not runnable by
  the ggml backend. Collapsing the two is how the original bug (real models
  silently absent from `/v1/models`) comes back.
- **The stub contract is frozen.** `slang_implemented_phase()` is `"A1"` and
  `slang_missing_inference_phases()` is `["A3","A4","A5"]` because the ggml
  backend routes AROUND the native path rather than implementing it. The
  ggml-backed path announces itself separately with `"stub":false` and
  `"backend":"ggml"`.

## OpenAI HTTP surface: supported vs not (live-verified 2026-11-16, Windows, Qwen2.5-1.5B)

Spec: `test/03_system/lib/slang/feature/slang_openai_conformance_live_spec.spl` (passing, 14 cases;
the former `..._in_development_spec.spl` cases 2/3/5 moved into it when they went green; bug
`doc/08_tracking/bug/slang_openai_stop_stream_finish_reason_unimplemented_2026-11-15.md`, fixed).

| Feature | Status |
|---|---|
| `POST /v1/chat/completions` non-stream, system/multi-turn messages | works |
| `POST /v1/completions` (raw prompt, `text_completion`) | works |
| `GET /v1/models`, `GET /health` | works |
| 400 malformed/missing messages, 404 `model_not_found` / `not_found`, 405 | works (OpenAI error envelope) |
| temperature 0 repeat identical, two concurrent connections | works |
| `finish_reason: "length"` on `max_tokens` | works (`stop` for end-of-turn / stop sequence) |
| `stop` (string or array) | works: cut before the earliest match, partial matches held back |
| `stream: true` (SSE) chat + completions | works; ggml lane streams per token, pure runner / shared-context backend answer with one content frame |
| `stream: true` with image/audio parts | 400 `unsupported_modality` (media path is not incremental) |
| `temperature`/`top_p`/`seed`/`n` | ignored (greedy) |

### How finish_reason / stop / streaming are built (2026-11-16)

- Decode loop is a step API in `model_executor/backend.spl`: `GenStream` + `gen_stream_step` (one sample, detokenize,
  eval; `stop_scan` from `pure/stop.spl` applies `stop`; `finish_reason` "stop" = EOG token or stop sequence, "length" =
  token budget). `_sample_loop` (non-stream) is just that step in a loop, so both paths share one set of semantics.
  `generate_stream_open` / `gen_stream_close` hold the per-request ggml context across steps; no C shim change was needed.
- `llm_engine.spl`: `EngineChatResult.finish_reason`, `engine_complete_{chat,text}_stops`, `engine_can_stream`,
  `engine_stream_open/step/close`. The pure runner applies `stop` to its finished text; "length" when completion tokens hit the cap.
- `serving_stream.spl` writes SSE straight to the connection (role frame, `choices[].delta` frames, final frame with
  `finish_reason`, `data: [DONE]`, no Content-Length, then close). `SimpleHttpServer.with_stream_handler` is the hook
  (called with the parsed request + live `TcpStream` before routing). The transport-free `slang_api_dispatch` still
  answers `stream:true` with 400 because it cannot stream.
- Mid-stream failures emit an error event then `[DONE]`; a client disconnect closes the request context.
- Time-to-first-token (Qwen2.5-1.5B Q4_K_M, CPU, "Count from 1 to 10.", max_tokens 24): first content frame at
  ~1.8 s (role frame 1.7 s, i.e. after prefill + first token), last frame at 3.65 s; the same request non-stream returns at
  2.7 s (it ran second, with the prompt prefix already cached, so the totals are not like for like). Streaming wins on
  perceived latency (first text at ~half the stream total) not on total time. Numbers printed by case 5
  (`SLANG_OPENAI case5 first_content_ms=... total_ms=... non_stream_total_ms=...`).

## Current limits

- ggml lane: GGUF only. Safetensors Llama (MHA) is served by the pure runner (see Runner dispatch); other safetensors (BF16, NVFP4, GQA) is recognised and refused.
- One model, one context, greedy sampling, one request at a time.
- No continuous batching (master plan A5). Prefix caching DOES exist: the
  serial exact-prefix snapshot cache (S1-S3, shim `slang_prefix_*`) is on by
  default at 4 entries / 2 GiB, works with stock llama.cpp, and is toggled with
  `engine_set_prefix_cache_limits(0, 0)` / `(4, 2147483648)`. Live receipt:
  `test/03_system/lib/slang/feature/slang_kv_cache_live_spec.spl` and the
  2026-11-14 table in `test/05_perf/slang_kv_cache/README.md` (Qwen2.5-1.5B,
  CPU: exact repeat re-prefills 1 of 988 prompt tokens, ~40x faster request).
  A hit is byte-identical to a full prefill: the shim decodes the last prompt
  token alone on the cold and hit path alike (`slang_ggml_request_eval_prompt`),
  so its logits come from one batch shape (fixed drift,
  `doc/08_tracking/bug/slang_prefix_cache_hit_output_drift_2026-11-14.md`).
  The physical paged-KV lane needs a llama.cpp with `include/llama-slang-paged.h`.
- Tree (radix) prefix cache, opt-in (2026-11-19): `engine_set_prefix_cache_mode(3, 0)` before load = one persistent multi-sequence context, per-sequence KV streams, byte-identical to no-cache greedy (modes 1/2 use unified KV and are NOT exact). Telemetry `engine_tree_cache_stats()`. Numbers + logs: `test/05_perf/slang_kv_cache/README.md`; bug `slang_shim_tree_kv_unified_modes_not_exact_2026-11-19.md`. Snapshot remains default; requests serialised per model (second tree request gets BUSY).

- The HTTP path is unreachable on the bootstrap seed; see
  `doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`
  and `doc/08_tracking/bug/seed_http_server_handle_connection_dispatch_2026-09-04.md`.

## Runner dispatch: pure runner or llama.cpp wrapper (2026-11-15)

```
slang -> pure LLM runner    src/lib/gc_async_mut/slang/model_executor/pure/   (safetensors Llama)
slang -> llama.cpp wrapper  model_executor/backend.spl + slang_ggml shim       (GGUF)
```

- **Dispatch point:** `engine_complete_chat` in `engine/llm_engine.spl` (and
  `engine_ensure_loaded` for preload) calls `select_runner`
  (`engine/runner_dispatch.spl`). GGUF -> `RunnerKind.Ggml`; safetensors whose
  `config.json` is `LlamaForCausalLM` with MHA (no GQA) and a single
  `model.safetensors` + `tokenizer.json` -> `RunnerKind.Pure`. `SLANG_RUNNER=pure|ggml`
  forces; an impossible forced choice (pure on GGUF, ggml on safetensors) or any
  other value is an explicit 503 `model_not_runnable`, never a fallback.
- **Pure lane** (`engine/pure_lane.spl`): `llm_engine` owns one `PureLane`
  (model + tokenizer + ONE `KvSession`) across requests, so a request sharing a
  token prefix re-uses cached K/V rows. `engine_pure_stats()` exposes the last
  request's reused / evaluated positions; `engine_last_runner()` says which
  runner served the last chat. Loading either lane unloads the other.
- **No chat template on the pure lane:** the prompt is the non-empty message
  contents joined by newlines (`chat_plain_prompt_from_body`); a single message
  is passed as-is. Greedy only; generation is bounded by the model's context.
- **Usage counts are real** for both runners (`EngineChatResult.prompt_tokens` /
  `completion_tokens`; the ggml count comes from `BackendGeneration.prompt_tokens`).
- **GPU seam:** a GPU variant of the pure runner plugs in at `RunnerKind.Pure`
  / `pure_lane_load`; `pure_runner_unsupported_reason` is its load gate.
- Evidence: `test/03_system/lib/slang/feature/slang_runner_dispatch_live_spec.spl`
  (`SLANG_LIVE=1 SLANG_MODEL_ROOT=C:/dev/model SLANG_GGML_LIB=build/sffi/slang_ggml.dll`).
  The seed interpreter runs the pure lane at ~0.1 token/s; set
  `SIMPLE_TIMEOUT_SECONDS=3600`.

## Upgrade path to pure Simple

Replace the ggml backend behind the same
`open`/`load_model`/`open_context`/`generate`/`close` surface in
`backend.spl`. That is master plan A3 (streaming loader), A4 (paged KV cache +
paged attention) and A5 (scheduler + worker). Callers do not change when the
backend does — that is what the seam is for.

## Verified end to end (2026-09-16, GB10 host)

- Models on disk under `/home/yoon/dev/model`: `Qwen3-Coder-Next-Q4_K_M`
  (4-shard GGUF, 46G) and `Qwen3.5-9B-Q3_K_M` (4.7G, unsloth GGUF) both
  generate through `slang_local` → caret; safetensors models (GLM-4.7-Flash,
  Qwen3.5-122B-NVFP4) are refused with a typed reason. Architecture support
  follows the linked llama.cpp (`qwen35` graph builders present at rev
  `f9f09f02c`, 2026-09-03).
- Working one-shot: `SLANG_MODEL_ROOT=/home/yoon/dev/model bin/caret
  --provider slang_local --model <dir> --prompt "..."`. Without
  `SLANG_MODEL_ROOT` caret scans `models/` and reports "model not found".
- Evidence gate: `sh scripts/check/check-slang-ggml-inference.shs --models
  /home/yoon/dev/model` → PASS (5/5 verdicts, 1 generated, 4 typed refusals).

### Operational traps confirmed today

- **Gate signals**: `check-slang-ggml-inference.shs` runs each model in the
  background and `wait`s, so HUP/INT/TERM exit 129/130/143 at once, kill the
  model run and remove the work dir (a foreground child deferred the trap and
  orphaned the run; verified TERM -> 143, no child left, 2026-11-15).
- **Shim symbol drift**: `backend.spl` at origin/main dlsyms 17 symbols
  including `slang_ggml_capabilities`; a shim built from older source exports
  14 and the TUI dies with `spl_dlsym: unresolved symbol`. Rebuild with
  `sh scripts/check/build-slang-ggml-shim.shs` in the tree you run from
  (50 symbols exported as of 2026-09-16). Never share one `libslang_ggml.so`
  across trees at different revisions.
- **Stale seed kills the TUI**: `rt_atexit_install` was unregistered in
  interpreters built before 2026-09-07
  (`doc/08_tracking/bug/caret_tui_mode_dies_rt_atexit_install_unregistered_2026-09-06.md`).
  The sealed seed at `src/compiler_rust/target/bootstrap/simple` (2026-09-08)
  has the fix; older `bin/simple` symlinks may not.
- **`--prompt` is one-shot by design** — no tool loop. The agent loop
  (`run_agent_loop`) only runs in the TUI. Headless: start the TUI inside
  tmux and drive it with `tmux send-keys`; see
  `doc/07_guide/app/llm/local_llm_slang_caret_setup.md`.
- **Fresh worktrees have no `build/sffi/`** — the engine default
  `build/sffi/libslang_ggml.so` resolves relative to cwd, so run the shim
  build script in the worktree (also fixes the `2>/dev/null`-silent
  "GGUF recognised but no ggml backend library is configured" error).

## Server run recipe, caret wiring, caret suite (verified 2026-11-12, GB10)

```bash
cd <worktree> && SIMPLE_RUST_SEED_WARNING=0 SIMPLE_TIMEOUT_SECONDS=0 \
  <seed> run src/app/slang_server/main.spl -- \
  --plaintext-development --models=/home/yoon/dev/model --port=8721 --n-ctx=32768
```

- Endpoints `GET /v1/models`, `POST /v1/chat/completions`; model loads lazily on
  the first completion. Test with `nc` (curl/wget are hook-blocked).
- caret → server: config `defaults: provider: slang` + `slang: base_url:
  http://127.0.0.1:8721`, `model: <dir>`; run `main.spl --config <file>
  --workspace <worktree> --dangerously-allow-all`. `slang` = HTTP client
  (`SLANG_BASE_URL`), `slang_local` = in-process (`SLANG_MODEL_ROOT`).
- caret suite: `bin/cs [session]` inside tmux; `/launch <spec> [args...]`
  (args appended verbatim, space-split), `/switch /max /key /kill /agents`.
  Spec `harness[:provider][/model]`; one worktree + `work/<topic>` branch + PR
  per agent. Keep briefs short; a 30B model cannot digest `spipe.md`.

### Traps
- **Stale seed:** before 2026-11-09 (`afb36d2e0a5`) HTTP hangs in CLOSE-WAIT;
  without PR #8492 the memory gate reads `/proc/meminfo` as "" (fsync EINVAL on
  procfs counted as a close failure in `rt_io_file_close`) and refuses every
  model; `--n-ctx` is also missing. Rebuild: `cd src/compiler_rust && cargo build
  --release --bin simple`.
- **cgroup + CUDA:** never run the server under `systemd-run -p MemoryMax=`; the
  GB10 CUDA context is charged to the cgroup and `ggml_cuda_init` fails OOM.
- **nvcc host clang:** nvcc 13.0 rejects clang >= 21; build llama.cpp with
  clang-18 (`CMAKE_CUDA_HOST_COMPILER`), see the guide.
- **Default ctx is 4096:** too small for a caret agent; pass `--n-ctx=32768`.
- **Open:** intermittent CUDA OOM when a second CUDA process starts while one
  holds a model (aborts the server; single-server/two-client fix in progress);
  JIT demotions to the interpreter (`_first_safetensors` bare `dir_list`;
  caret `telemetry().active_requests` inferred as `RingTelemetry`). Both still work.

## Windows (llvm-mingw) (verified 2026-11-14, Windows 11, CPU)

- **Build:** llama.cpp with llvm-mingw, `BUILD_SHARED_LIBS=ON`, into
  `$LLAMA_ROOT/build-mingw`; then
  `LLAMA_ROOT=/c/dev/tools/llama.cpp sh scripts/check/build-slang-ggml-shim.shs`.
  mingw is the Windows default; clang-cl/lld-link is opt-in via `SLANG_SHIM_MSVC=1`.
  `LLAMA_ROOT` is required on Windows (no Linux default).
- **DLL naming trap:** mingw produces `libllama.dll` (import lib
  `src/libllama.dll.a`), MSVC produces `llama.dll`/`llama.lib`. The mingw DLLs
  also import `libc++.dll`/`libunwind.dll` from llvm-mingw's
  `x86_64-w64-mingw32/bin`. The script copies all of them next to the shim and
  `backend.spl` `_preload_windows_dll_siblings` preloads them, so no PATH edit
  is needed. A missing sibling shows up only as "backend library could not be opened".
- **Compiler trap:** a bare `clang` on PATH may target MSVC (ROCm ships one);
  the script uses `$SIMPLE_MINGW_ROOT/bin/clang.exe` and checks `-dumpmachine`.
## Pure-Simple runner (no llama.cpp)

`src/lib/gc_async_mut/slang/model_executor/pure/`: `weights.spl` (safetensors),
`tensor_ops.spl` (the single compute seam; a GPU provider replaces only this),
`llama_forward.spl` (Llama-2 forward), `kv_cache.spl` (KvSession: per-layer K/V
rows, prefix reuse, `positions_evaluated` counter), `tokenizer.spl`
(SentencePiece-BPE from tokenizer.json). Not wired into the engine/server yet.
Measured on the seed interpreter, stories15M, "Once upon a time": generated
text matches llama.cpp greedy; about 0.12 tokens/s. Fixture
`test/fixtures/slang_pure/stories15m_generate.spl`; system spec
`slang_pure_kv_cache_spec.spl`.

### Sampling, stop, generation loop (pure runner)
- `sampler.spl`: `sampler_sample(cfg, state, logits, recent)` -> token + next state. Order penalty -> temperature -> top-k -> top-p -> draw; temperature <= 0 is `tensor_argmax`. PRNG = minstd in `SamplerState` (seed -> same tokens, no globals). top-k = insertion selection (no vocab sort); top-p alone = log-prob bucket histogram + sort of the boundary bucket only (an earlier growing-top-K version took ~300 s/token on a flat 32000 vocab; fixed). Measured on the seed, vocab 32000: top-k 40 ~0.3 s/token, top-p 0.9 ~1.0 s, plain temperature ~0.6 s.
- `stop.spl`: EOS ids, token budget, stop strings on decoded text; `stop_scan` truncates before the earliest match and reports `hold_back` (trailing units that may start a stop string; never stream them). Offsets are `len()/substring()/index_of()` units (code points on the current seed), stop strings assumed ASCII.
- `generate.spl`: `gen_begin` (Err on empty/oversize prompt; prefix reuse, last prompt token always re-evaluated) + `gen_next` (one token, `delta` = text safe to stream) + `generate` (loop; returns `pieces`, `finish_reason` "stop"|"length", prompt/completion token counts, positions evaluated/reused). At temperature 0 ids equal `kv_generate_greedy` (EOS id included, no text). `kv_cache.spl` untouched.
- Specs: unit `sampler_spec`, `stop_spec`, `generate_spec` (tiny synthetic model); system `slang_pure_sampling_spec.spl` (stories15M, gated on the model dir).
Seed pitfalls found: an f64 carried through `Result` + `?` is mis-unboxed (parse
numbers after the `?`); tokenizer.json escapes include `\r`.

## Related

`doc/05_design/ml/slang/slang_master_plan.md`,
`doc/07_guide/app/llm/local_llm_slang_caret_setup.md`,
`doc/08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md`.

## GPU (Vulkan, AMD)

Build and run the shim against a Vulkan llama.cpp (llvm-mingw, Radeon 8065S verified 2026-11-15):

```bash
LLAMA_ROOT=/c/dev/tools/llama.cpp LLAMA_BUILD_DIR=$LLAMA_ROOT/build-mingw-vulkan \
  SLANG_SHIM_OUT_DIR=$PWD/build/sffi-vulkan sh scripts/check/build-slang-ggml-shim.shs
SLANG_LIVE=1 SLANG_GPU=1 SLANG_MODEL_ROOT=C:/dev/model SLANG_GGML_LIB=build/sffi-vulkan/slang_ggml.dll \
  bin/simple test test/03_system/lib/slang/feature/slang_gpu_offload_live_spec.spl
```

- `ggml-vulkan.dll` is copied beside the shim and preloaded by `_preload_windows_dll_siblings`.
- Engine default is all layers on the GPU; `engine_set_gpu_layers_text("0")` (before load) keeps the CPU lane.
- Evidence: shim `slang_ggml_gpu_offload_supported` / `slang_ggml_model_offloaded`, surfaced as `engine_gpu_offload_status()`; the llama log shows `using device Vulkan0` and `offloaded 29/29 layers to GPU`.
- On GPU the prefix cache restores only partly (988 -> 512 re-prefilled tokens on exact repeat; first-micro-batch workaround), and wall time is noisy.
## Live consumer system specs (2026-11-15)

- `test/03_system/lib/slang/feature/slang_caret_local_usage_spec.spl` drives caret's
  `dispatch_send("slang_local", ...)` (base_url = model root, cli_path = shim) against the
  real 1.5B model; asserts provider `slang_local/ggml`, non-empty text, and a second request.
- `slang_http_server_live_spec.spl` spawns `src/app/slang_server/main.spl` via
  `process_spawn_redirected`, speaks HTTP over `TcpStream`: /v1/models, two chat
  completions, 404 `model_not_found`, then `process_kill_tree`. ~25 s server startup.
- Gate: `SLANG_LIVE=1 SLANG_MODEL_ROOT=C:/dev/model SLANG_GGML_LIB=build/sffi/slang_ggml.dll
  SIMPLE_BINARY=<simple>`; model dir name from `CARET_SLANG_MODEL`
  (default `Qwen2.5-1.5B-Instruct-Q4_K_M`). Ungated they skip.
- Known gap: server `usage` counts are always 0
  (`doc/08_tracking/bug/slang_openai_usage_counts_always_zero_2026-11-15.md`).
- **Windows test-lane notes.** `check_fit_with_available` is `check_fit` against an
  availability the caller already probed (two Windows probes drift ~270 MB, so specs
  probe once). Shell gates on MSYS must avoid per-file `$(...)` pipelines: a spawn costs
  seconds there. The conformance test drops `detect_leaks` on Windows (no LSan) and the
  prefix-cache contract test uses llvm-mingw clang there, as `build-slang-ggml-shim.shs` does.
## ROCm GPU ops provider (pure runner)
- Layering: pure runner -> GPU API -> ROCm. Backend: `src/lib/gc_async_mut/gpu/rocm/hip_compute.spl` (HIP + hipRTC via `spl_dlopen`/`spl_wffi_call_i64`; launch through `hipDrvLaunchKernelEx`, 4 int args, so no wide C shim). Ops: `pure/tensor_ops_rocm.spl` (device-resident f32 `RocmTensor`; matvec, rmsnorm, add, mul, silu, attention; all `Result<_, text>`). Weights upload once; CPU `tensor_ops.spl` is untouched.
- Specs: `test/01_unit/lib/gc_async_mut/slang/model_executor/pure/tensor_ops_rocm_spec.spl`, `test/03_system/lib/slang/feature/slang_pure_rocm_ops_spec.spl` (skip with reason when `C:\Program Files\AMD\ROCm\7.2\bin` DLLs are absent).
- Weights go to the device as raw F32 bytes (`rocm_tensor_upload_f32_bytes`, ranges from `pure_weights_f32_ranges`): the 32000x288 head uploads in ~23 ms (was ~330 s with per-element f64->f32 staging). Downloads are bulk bytes but decoded per element in the seed interpreter (~2 s for 32000 values), so keep reductions such as argmax on device. `hip_compute.spl` declares no `rt_*` externs (libc malloc/memcpy via `spl_wffi_*`, reads via `sffi.raw_bytes`). `SLANG_ROCM_BIN` overrides the ROCm bin dir.
- **Windows memory probe.** `mem_available_bytes()` uses `Win32_PerfFormattedData_PerfOS_Memory.AvailableBytes` (free+standby), not `FreePhysicalMemory`, which collapses after reading big model files and falsely refuses loads (`doc/08_tracking/bug/slang_windows_mem_available_uses_free_not_available_2026-11-15.md`). Runtime overhead in admission scales with n_ctx and model size (`estimate_runtime_overhead_bytes`).
## Multimodal input (image / audio / video; in progress, 2026-11-15)

- **Protocol (done):** `protocol.chat_messages_parse` keeps typed `ChatPart`s
  (`text`/`image`/`audio`/`video`); `image_url`/`input_audio`/`video_url` data
  URLs are strict-base64 checked, `http(s)` URLs are 400 `unsupported_media_url`.
  Media parts are never dropped: `serving_chat.media_refusal` answers 400
  `unsupported_modality` unless the resident model can take them. Each media part
  becomes `SLANG_MEDIA_MARKER` (`<__media__>`) in the chat frame.
- **Video:** refused with a clear error (no decoder, no ffmpeg subprocess).
- **Model dir:** `native_formats.gguf_is_projector` reads GGUF `general.architecture`
  (first KV, fixed offsets) == `clip`; `mmproj` filename prefix is only the
  fallback when the first key is another one. `gguf_entry_shard` never returns a
  projector; `NativeModel.mmproj_path` carries it; two projectors = refused.
- **mtmd path:** shim `mtmd group` block (end of `slang_ggml_shim.c`, bit 128,
  `-DSLANG_WITH_MTMD`, built with `SLANG_SHIM_MTMD=1 LLAMA_BUILD_DIR=<build with
  libmtmd>`): add_encoded (magic-sniffed jpeg/png/gif/bmp/wav/mp3/flac only, so
  video never reaches ffmpeg) -> chat render (markers) -> mm_tokenize ->
  mm_eval_prompt (clears KV; never touches the prefix cache). Engine loads the
  projector after the context; `engine_media_caps()` is what actually works.
  Media decode is C-side (stb_image/miniaudio); pure-Simple decoders are not wired.
- **Memory gate:** overhead is `estimate_runtime_overhead_bytes` (n_ctx- and model-scaled, no GGUF parse), so a small model at small context no longer needs ~10 GiB free; the per-token constant is an admission-only upper bound, not exact KV size.
- **Runner trap:** `skip(...)` inside an example is counted as PASSED
  (`skipped=0`); the live spec records `SKIPPED:` lines to `build/probe/mm_answers.txt`.
- **Live spec timeout knob:** `SLANG_RUN_TIMEOUT_MS` (default 600000) bounds each child in `caret_slang_local_hello_system_spec.spl`; the 3-model gate (`check-slang-ggml-inference.shs`, 9 dirs) took 34m50s on a loaded Windows host, so set e.g. 3300000 with `SIMPLE_TIMEOUT_SECONDS=3600`.

## Model variety live spec (2026-11-15, Windows, llvm-mingw shim)

`test/03_system/lib/slang/feature/slang_model_variety_live_spec.spl` loads each model under
`SLANG_MODEL_ROOT` through `engine_ensure_loaded` + `engine_complete_chat_observed` (chat template,
greedy) and asserts a Paris / `def ` answer; absent models print SKIPPED_BY_ABSENCE and skip.
`SLANG_GPU=1` selects the Vulkan pass (shim built with `LLAMA_BUILD_DIR=.../build-mingw-vulkan`)
and asserts the shim reports offload. 7/7 pass on CPU and GPU. Qwen3-ASR-0.6B is NOT refused: it
answers as a chat model (`language English<asr_text>The capital of France is Paris.`). Prompt
tokens are not exposed by the engine observation (column n/a). Load time is 64-120 s per model
for every size (`doc/08_tracking/bug/slang_model_load_fixed_overhead_70_100s_windows_2026-11-15.md`).
Tokens/s below is meaningless for 1-2 token answers.

| device | model | load ms | gen tok | gen ms | tok/s | answer |
|---|---|---|---|---|---|---|
| cpu | Qwen2.5-1.5B Q4_K_M | 88015 | 1 | 1505 | 0.6 | Paris |
| cpu | Qwen2.5-Coder-7B (capital) | 67198 | 1 | 16561 | 0.0 | Paris |
| cpu | Qwen2.5-Coder-7B (python) | 97686 | 96 | 40345 | 2.3 | ```python def add_numbers |
| cpu | gemma-3-270m Q8_0 | 85433 | 2 | 1218 | 1.6 | Paris |
| cpu | Llama-3.2-1B Q4_K_M | 73767 | 2 | 1312 | 1.5 | Paris. |
| cpu | SmolVLM2-256M Q8_0 | 120456 | 24 | 325 | 73.8 | The capital of France is Paris... |
| cpu | Qwen3-ASR-0.6B Q8_0 | 76604 | 10 | 2986 | 3.3 | language English<asr_text>...Paris. |
| gpu | Qwen2.5-1.5B Q4_K_M | 87879 | 1 | 1306 | 0.7 | Paris |
| gpu | Qwen2.5-Coder-7B (capital) | 74007 | 1 | 759 | 1.3 | Paris |
| gpu | Qwen2.5-Coder-7B (python) | 64216 | 96 | 2874 | 33.4 | ```python def add_numbers |
| gpu | gemma-3-270m Q8_0 | 76606 | 2 | 3271 | 0.6 | Paris |
| gpu | Llama-3.2-1B Q4_K_M | 86591 | 2 | 494 | 4.0 | Paris. |
| gpu | SmolVLM2-256M Q8_0 | 83498 | 24 | 199 | 120.6 | The capital of France is Paris... |
| gpu | Qwen3-ASR-0.6B Q8_0 | 95035 | 10 | 424 | 23.5 | language English<asr_text>...Paris. |
- Device forward pass (2026-11-15): `pure/llama_forward_rocm.spl` runs the stories15M Llama forward on the Radeon 8065S: `rocm_llama_load` (F32 byte-range upload once), `llama_step_rocm` (hidden state and per-layer K/V rows stay on the device; intermediates freed every step), `rocm_generate_greedy` (same prefix-reuse rule as `kv_cache.spl`, shared via `kv_reuse_len`; counts `positions_evaluated`). New device kernels in `tensor_ops_rocm.spl`: rope, kv_write (in place), row lookup, argmax (one i32 readback, never the 32000 logits). Spec: `slang_pure_rocm_generate_spec.spl` (GPU ids == CPU ids, reference text, prefix reuse, perf table in the log; needs `--timeout 3600` because the CPU leg is minutes on the seed). KV capacity is `min(max_position_embeddings, 1024)` (attention keeps scores in shared memory). `hip_compute.rocm_kernel` now destroys the hipRTC program on every path; the code-object buffer is deliberately kept (HIP docs do not say whether `hipModuleLoadData` copies it). `env_get` returns "" when unset, not None: `?? default` never fires.
- Integration (2026-11-16): `/v1/completions` goes through the same dispatch as chat (`engine_complete_text`) and returns real usage counts; a media request to a pure-runner model is refused (text only), never routed to ggml. Pure/dispatch/variety system specs append evidence and `SKIPPED: <why>` lines to `build/probe/*_evidence.txt` because the runner counts skip() as passed (bug records in doc/08_tracking/bug).

## Host portability (Windows / Linux / macOS, 2026-11-16)

One module owns every per-OS decision: `src/lib/gc_async_mut/slang/host/slang_host.spl`.
Decisions are pure functions of an `os` text (`ggml_lib_default`, `rocm_bin_default_for`,
`hip_lib_names`, `hiprtc_lib_names`, `host_libc_name`, `host_join`, and the parsers
`parse_meminfo_bytes`, `parse_vm_stat_page_size`, `parse_vm_stat_available_pages`,
`parse_int_text`, `darwin_available_bytes`), so the Linux/macOS branches are unit-tested on any host
(`test/01_unit/lib/gc_async_mut/slang/host/slang_host_spec.spl`). The `host_*` wrappers
route env, file exists/read, directory list and process capture through SOSIX
(`std.nogc_async_mut.sosix.host_facade`; `sosix_host_os()` is the three-way OS accessor).

- Lazy by construction: no native library is opened at import. The ggml shim is
  dlopen'ed by `open_backend` on the first model load, ROCm by `rocm_open_at` on first GPU
  use; `engine_backend_available()` is a file probe only (spec asserts the engine stays empty).
- Not SOSIX (no accessor exists): `spl_dlopen`/`dlsym`/`spl_wffi_call_*`, `file_size`,
  `is_dir`, byte reads (`file_read_bytes`), ranged text reads, sha256. They stay on
  `std.io_runtime` / `std.nogc_sync_mut.sffi.dynamic`.
- Library names: shim `slang_ggml.dll` / `libslang_ggml.so` / `libslang_ggml.dylib`;
  ROCm `amdhip64_7.dll`+`hiprtc0702.dll` (bin dir) vs `/opt/rocm/lib/libamdhip64.so[.7]`+`libhiprtc.so[.7]`;
  macOS has no ROCm (returns Err). CUDA is not loaded anywhere in slang. Windows path
  literals must escape every backslash: `"...\ROCm\7.2\bin"` unescaped turns `\7` into a
  control char and ROCm silently reads as absent (caught 2026-11-17 by the live ROCm spec).
- Free memory: Linux `/proc/meminfo` MemAvailable; macOS = vm_stat free + inactive +
  speculative pages (purgeable excluded: it overlaps active/inactive) times the page size from
  vm_stat's OWN header (`hw.pagesize` only as fallback; Rosetta sees 4 KiB vs native 16 KiB),
  capped at `sysctl hw.memsize` (no pipe/awk, parsed in Simple; this also removed the
  W-STR-BRACE-001 warning); Windows
  `Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory`. Probes run with NO timeout
  (the CIM probe has measured 54-135 s under load).
- Shim build (`scripts/check/build-slang-ggml-shim.shs`): Linux = clang (refuses a non-clang
  `CC`, never GCC) + `-fuse-ld=lld`; macOS = clang `-dynamiclib` (system ld64), `nm -gU` with the
  `_` prefix stripped; Windows lanes unchanged. Linux/macOS builds are unverified (no host).
