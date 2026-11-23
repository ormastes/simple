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
- Tree (radix) prefix cache, opt-in (2026-11-19): `engine_set_prefix_cache_mode(3, 0)` before load = one persistent multi-sequence context, per-sequence KV streams, digest-equal to no-cache greedy on the CPU build (bits unmeasured); NOT bit-exact on Vulkan, see `slang_tree_kv_gemma_branching_digest_differs_on_vulkan_2026-11-22.md` (modes 1/2 use unified KV and are NOT exact). Telemetry `engine_tree_cache_stats()`. Numbers + logs: `test/05_perf/slang_kv_cache/README.md`; bug `slang_shim_tree_kv_unified_modes_not_exact_2026-11-19.md`. Snapshot remains default; requests serialised per model (second tree request gets BUSY). Review fixes 2026-11-20: reuse capped by the owner's exact span, first-micro-batch warm-up, `BackendError.Busy`, refused mode fails the load (bug record).


- The HTTP path is unreachable on the bootstrap seed; see
  `doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`
  and `doc/08_tracking/bug/seed_http_server_handle_connection_dispatch_2026-09-04.md`.
  Under `SIMPLE_EXECUTION_MODE=interpret` the sync server does answer (2026-11-17).
- **Binary bodies (L2, 2026-11-17, re-review 2026-11-20).** `HttpRequest.body_bytes` holds
  the raw body on the scalar, vector and HTTP/2 paths. A non-UTF-8 body of a non-text type
  has `body` ""; text-ish types (`request_body_is_textual`: text/*, json, xml,
  form-urlencoded, js, ndjson, none) stay a 400 on the scalar path and keep the lossy decode
  on the vector and h2 paths. The first Content-Type header wins everywhere.
  `HttpResponse.bytes(status, content_type, data)` sets `body_bytes`; `write_response*`,
  `response_wire_size` (head in octets) and h2 send/count it as octets (`serialize_response`
  gives "" for a non-UTF-8 binary body). `http_server.handler.parse_multipart_bytes(body,
  content_type)` returns `MultipartPart{name, filename, content_type, data: [u8]}`:
  line-anchored delimiters with padding, empty parts, 16 KiB part-header cap.
  `serving_stream.slang_http_response(ApiResponse)` is the one ApiResponse->HttpResponse
  map (router and the stream path's JSON refusals, which now go through
  `write_response_limited` with security headers). Slang caps: body 64 MiB, response
  `SLANG_MAX_RESPONSE_BYTES` = 64 MiB + 64 KiB head room (library 10 MiB / 16 MiB).
  FFI byte helpers: `std.nogc_sync_mut.sffi.dynamic` exports `spl_wffi_call_i64_with_bytes`,
  `spl_wffi_call_i64_into_bytes` and `bytes_zeroed(n) -> [u8]?` (packed, n <= 256 MiB);
  `std.nogc_sync_mut.io_runtime.file_read_bytes_at(path, offset, size) -> [u8]?`;
  SOSIX `sosix_process_run_bounded_bytes`, `sosix_process_owned_start_v3`,
  `sosix_process_owned_start_pinned_v3`.

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
## Cross-kind system spec (2026-11-22)
- `test/03_system/lib/slang/feature/slang_system_all_kinds_live_spec.spl` runs these through `slang_api_dispatch` on Vulkan: /v1/models, chat with KV off/on, vision, video, asr, image_gen, embeddings + rerank, and tts. It writes `SYSTEM` / `SYSTEM_KV` rows to `build/probe/slang_system.txt`.
- The KV prompt stays under 512 tokens (Gemma-3 `n_swa`). The snapshot cache reuses nothing on SWA models past the window. The video clip is 4:3, because a square frame tiles to 17x64 positions and 4 frames overflow 4096. Both are recorded in `doc/08_tracking/bug/slang_snapshot_prefix_cache_swa_long_prompt_2026-11-22.md`.
## ROCm GPU ops provider (pure runner)
- Layering: pure runner -> GPU API -> ROCm. Backend: `src/lib/gc_async_mut/gpu/rocm/hip_compute.spl` (HIP + hipRTC via `spl_dlopen`/`spl_wffi_call_i64`; launch through `hipDrvLaunchKernelEx`, 4 int args, so no wide C shim). Ops: `pure/tensor_ops_rocm.spl` (device-resident f32 `RocmTensor`; matvec, rmsnorm, add, mul, silu, attention; all `Result<_, text>`). Weights upload once; CPU `tensor_ops.spl` is untouched.
- Specs: `test/01_unit/lib/gc_async_mut/slang/model_executor/pure/tensor_ops_rocm_spec.spl`, `test/03_system/lib/slang/feature/slang_pure_rocm_ops_spec.spl` (skip with reason when `C:\Program Files\AMD\ROCm\7.2\bin` DLLs are absent).
- Weights go to the device as raw F32 bytes (`rocm_tensor_upload_f32_bytes`, ranges from `pure_weights_f32_ranges`): the 32000x288 head uploads in ~23 ms (was ~330 s with per-element f64->f32 staging). Downloads are bulk bytes but decoded per element in the seed interpreter (~2 s for 32000 values), so keep reductions such as argmax on device. `hip_compute.spl` declares no `rt_*` externs (libc malloc/memcpy via `spl_wffi_*`, reads via `sffi.raw_bytes`). `SLANG_ROCM_BIN` overrides the ROCm bin dir.
- `std.compute` HIP reduce offload (2026-11-22): `src/lib/gc_async_mut/gpu/rocm/hip_reduce.spl` (exact i64 reduce kernel, ops add/mul/min/max/xor/and/or, one 256-thread block, compiled with hipRTC on first use; device cached per ROCm dir) is what `backend_dispatch.spl` now calls for a HIP target. `gpu_payload_present("hip")` calls `hip_reduce_device()`. It does a library file check first (nothing loads when ROCm is absent), then opens HIP (hipInit plus the device name), so an install with no GPU is not HIP-present. The API takes `HipReduceRequest(data, init, op: HipReduceOp)`. The device cache assumes a single-threaded caller. Required HIP with no ROCm fails closed with `gpu-backend-unavailable:hip`; suggested HIP resolves to the CPU. Spec: `test/03_system/lib/gpu/hip_reduce_offload_spec.spl` (evidence in `build/probe/hip_reduce_evidence.txt`).
- **Windows memory probe.** `mem_available_bytes()` uses `Win32_PerfFormattedData_PerfOS_Memory.AvailableBytes` (free+standby), not `FreePhysicalMemory`, which collapses after reading big model files and falsely refuses loads (`doc/08_tracking/bug/slang_windows_mem_available_uses_free_not_available_2026-11-15.md`). Runtime overhead in admission scales with n_ctx and model size (`estimate_runtime_overhead_bytes`).
## Multimodal input (image / audio / video; in progress, 2026-11-15)

- **Protocol (done):** `protocol.chat_messages_parse` keeps typed `ChatPart`s
  (`text`/`image`/`audio`/`video`); `image_url`/`input_audio`/`video_url` data
  URLs are strict-base64 checked, `http(s)` URLs are 400 `unsupported_media_url`.
  Media parts are never dropped: `serving_chat.media_refusal` answers 400
  `unsupported_modality` unless the resident model can take them. Each media part
  becomes `SLANG_MEDIA_MARKER` (`<__media__>`) in the chat frame.
- **Video (L7):** `modality/video_frames.spl` `sample_frames(blob, n)`. With
  `SLANG_FFMPEG=<path to ffmpeg.exe>` set and a projector model, `serving_chat.expand_video_parts`
  replaces each `video_url` part by n JPEG `image` parts (default 4 because 8 SmolVLM2 frames overflow n_ctx 4096; `SLANG_VIDEO_FRAMES`, 1..32; 384 px edge;
  duration and fps from `ffmpeg -i`, then `select` of the frame on screen at (k+0.5)*dur/n with
  `-fps_mode passthrough` (ffmpeg >= 5.1), so a one-frame clip yields one frame; unknown duration = 1 fps
  over the first 64 s, n picked evenly) -> mjpeg image2pipe split on SOI/EOI. A probe spawn failure/timeout
  is a server fault (503) and stops before the main run. ffmpeg runs via `slang_host.host_run_bounded_bytes`
  (TODO `slang-sosix-bytes-run`: SOSIX has no bytes run). `slang_video_live_spec` has an ffmpeg-only example (no GPU). Temp file `slang_video_<16 random hex>_<us>.bin`
  through `slang_host` (`host_temp_dir`, `host_file_write_bytes`, `host_file_delete`, `host_random_hex`), removed on every path.
  Video >10 MiB decoded = 413 `request_too_large`; `SLANG_FFMPEG` not a file = 503; no frame = 400
  `invalid_media`. With no `SLANG_FFMPEG` the old 400 `unsupported_modality` text is kept verbatim.
  Static build: `C:/dev/tools/ffmpeg` (gyan.dev essentials, sha256-verified). Live: `slang_video_live_spec.spl`.
- **Model dir:** `native_formats.gguf_is_projector` walks the GGUF KV block as
  binary (`modality/kind_registry.gguf_facts`): `general.architecture == clip` or
  `general.type == mmproj`; the `mmproj` filename prefix is only the fallback when
  the metadata names neither. `gguf_entry_shard` never returns a projector or a
  `wavtokenizer-dec` vocoder; `NativeModel.mmproj_path` carries the projector;
  two projectors = refused.
- **mtmd path:** shim `mtmd group` block (end of `slang_ggml_shim.c`, bit 128,
  `-DSLANG_WITH_MTMD`, built with `SLANG_SHIM_MTMD=1 LLAMA_BUILD_DIR=<build with
  libmtmd>`): add_encoded (magic-sniffed jpeg/png/gif/bmp/wav/mp3/flac only, so
  video never reaches ffmpeg) -> chat render (markers) -> mm_tokenize ->
  mm_eval_prompt (clears KV; never touches the prefix cache). Engine loads the
  projector after the context; `engine_media_caps()` is what actually works.
  Media decode is C-side (stb_image/miniaudio); pure-Simple decoders are not wired.
- **Memory gate:** overhead is `estimate_runtime_overhead_bytes` (n_ctx- and model-scaled, no GGUF parse), so a small model at small context no longer needs ~10 GiB free; the per-token constant is an admission-only upper bound, not exact KV size.
- **Runner trap:** `skip(...)` inside an example is counted as PASSED
  (`skipped=0`) by seeds without the 2026-11-23 `bdd.rs` fix (source now counts it
  skipped and prints `○ name (skip in body)`; bug doc
  `spec_skip_reported_as_pass_2026-11-19`; keep the `SKIPPED:` lines until the seed is redeployed); the live spec records `SKIPPED:` lines to `build/probe/mm_answers.txt`.
- **Live spec timeout knob:** `SLANG_RUN_TIMEOUT_MS` (default 600000) bounds each child in `caret_slang_local_hello_system_spec.spl`; the 3-model gate (`check-slang-ggml-inference.shs`, 9 dirs) took 34m50s on a loaded Windows host, so set e.g. 3300000 with `SIMPLE_TIMEOUT_SECONDS=3600`.

## Model kinds and modalities (L1 common structure, 2026-11-17)

Design: `doc/05_design/ml/slang/slang_pluggable_modalities.md`.
- `slang/modality/kinds.spl`: `Modality`, `ModelKind` (Chat Asr Tts ImageGen
  Embedding Rerank), `KindProfile`, `OutputPart`, `KindParams`, `KindRequest`,
  `KindResult`. `RunnerKind` (runner_dispatch) gained `Whisper`, `StableDiffusion`.
- `kind_registry.resolve_kind(dir)` chain: `slang_kind.sdn` (`kind:`, `vocoder:`)
  -> one projector (inputs from `clip.has_vision_encoder` / `has_audio_encoder`)
  -> vocoder companion = Tts -> `<arch>.pooling_type` (4 rerank, 1-3 embedding)
  -> no pooling type on an embedding-table arch: a `cls.output.weight` /
  `cls.weight` tensor in the tensor-info table = Rerank -> arch table (bert,
  nomic-bert, jina-bert-v2 = embedding; flux, sd1, sd2, sdxl, sd3, aura,
  t5encoder = ImageGen on stable-diffusion) -> magic (`lmgg` WITH whisper.cpp
  hparams `n_audio_ctx 1500`, `n_mels 80|128` = Asr/whisper; a legacy llama
  ggml file shares `lmgg` and is NOT Asr; `model.diffusion_model.` safetensors
  = ImageGen) -> LlamaForCausalLM = Chat/pure. `NativeModel.profile` carries it
  (default: Chat [text] ggml). The deciding GGUF is the lowest-named model file
  that names an architecture (split shard 1), not listing order.
  `kind: "tts"` (quoted) equals `kind: tts`.
- **Real reranker:** `bge-reranker-v2-m3-Q8_0.gguf` writes NO `bert.pooling_type`
  and no classifier KV (35 keys dumped); only its `cls.*` tensors mark it.
  `bge-small-en-v1.5` has `pooling_type 2` and no `cls.*`. The cheap KV walk
  stops at the first `tokenizer.` key; an embedding-arch model without a pooling
  type gets a second, FULL walk (vocab + tensor table, 6.8 MB header for the
  reranker): real file -> `arch=bert pooling=-1 cls_head=true`, whole
  `simple-release.exe run` probe 1.9 s. A failed full walk keeps the cheap facts.
- **Header reads:** one growing buffer per file, each step a ranged read of
  ONLY the bytes past it (the full rerank walk reuses the cheap walk's buffer);
  `gguf_facts` is cached per (path, size, mtime) in a copy-on-write snapshot
  (no lock; mtime 0 never cached), so /v1/models, chat_prepare's root scan and
  kind_mismatch do not re-walk headers per request. `gguf_header_bytes_read()`
  counts bytes read (spec: a 42 KB header reads exactly its size once, 0 on repeat).
- **Hostile GGUF:** every key/string/array/tensor-name length and
  `kv_count`/`tensor_count` is bounded by the bytes left in the FILE
  (`_fits`; arrays divide before multiplying); past the file = Malformed, past
  the bytes in hand = NeedMore (growing read). A top-bit u64 is a negative i64
  and is refused. A Malformed GGUF with the magic is still kept (Chat, empty facts).
- **Chat-path runnable:** `describe_model` marks any non-Chat kind not runnable
  (reason = why the kind is not served) and keeps a Chat profile's reason (an
  invalid `slang_kind.sdn`, e.g. `kind: embeddings`) as a not-runnable reason, so
  `llm_engine` / `entrypoints/llm` never load an embedder or a typo'd model as chat.
  The FORMAT's reason wins otherwise ("safetensors recognised; ...", "slang
  pack recognised; ..."): the resolver's "no kind could be resolved" replaces
  it only when the format found nothing wrong or an override was refused.
- Kind routes resolve a slang pack by its manifest `model_id` (as /v1/models
  lists it) -> 400 `wrong_model_kind`; an empty / unknown-format dir is not a
  model -> 404.
- Model-root `slang_kind.sdn` overrides are NOT in git (model dirs live outside
  the repo). bge-reranker-v2-m3 needs none: its `cls.output.weight` tensor
  (full tensor-table walk when no pooling_type is written) makes it Rerank.
- `/v1/models` entries add `slang_kind`, `input_modalities`, `output_modalities`
  (`scan_model_root(C:/dev/model)` 573 ms vs 229 ms before kinds, 12 dirs, seed;
  each describe walks every GGUF header once, first read 4 KiB). `ApiResponse` gained `content_type`
  (default `application/json`) and `body_bytes` (default empty = text body).
- Kind paths `api_server.kind_route_paths` (non-chat only; any other path 404);
  `entrypoints/openai/serving/` holds one
  stub per family (`serve_transcriptions`, `serve_speech`, `serve_images`,
  `serve_embeddings`, `serve_rerank`): wrong kind = 400 `wrong_model_kind` (chat
  routes too, by describing only the named directory; `kind_serves` also lets a Chat model with Audio input serve Asr), right kind = 501 `not_implemented` naming the runner
  (formerly `engine/kind_dispatch.kind_open`; deleted once every kind route was served).
- L1 host access goes through `slang/host/slang_host` only: `host_file_exists`,
  `host_file_read`, `host_dir_list`, `host_env` (SOSIX) and `host_file_size`,
  `host_file_mtime`, `host_is_dir`, `host_read_bytes_at` (no SOSIX accessor
  yet; the single place to swap). slang_host_spec pins that kind_registry and
  serving_models import no io_runtime / external_file primitive.
- Spec: `test/01_unit/lib/gc_async_mut/slang/kind_registry_spec.spl`.

## Shim bulk I/O, model handles, embeddings (L4, 2026-11-18)

- **Bit 256 bulk I/O:** `slang_ggml_[request_]str_push_bytes(ptr, len)` (via
  `spl_wffi_call_i64_with_bytes`) and `slang_ggml_[request_]out_into(buf, cap,
  out_len)` (via `spl_wffi_call_i64_into_bytes`; cap 0 = size probe, too-small
  cap = -4 with `out_len` set). `backend.spl` `_push_text`/`_read_out` and the
  request variants use them when the bit is set and keep the per-byte loop for
  an older shim. `_sample_loop` reuses one 4096-byte piece buffer.
  `into_bytes` is declared locally in `backend.spl` until L2 exports it (G1);
  `_out_buffer` is a packed-buffer stand-in until L2's `bytes_zeroed` (G5).
- **Bit 512 model handles:** `slang_ggml_model_open(path_bytes, n_gpu_layers)`
  loads a model BESIDE the default `g_model` (max 4; same path returns the same
  handle), `model_close(h)` (-9 while a request on it is open),
  `request_create_for(h, n_ctx)` (h 0 = default). Each request carries its
  model; tokenize/piece/chat_render use it. Handle requests never touch the
  prefix cache. Backend API: `open_model_handle`, `open_request_for`,
  `close_model_handle`.
- **Embeddings/rerank:** `request_embed_configure(r, pooling)` rebuilds the
  context with `embeddings=true`, `n_ubatch = n_ctx` (pooling -1 model default,
  0 none, 1 mean, 2 cls, 3 last, 4 rank). `request_embed_eval` decodes ALL
  tokens in one batch, every position output (not eval_prompt: that splits off
  the last token). `request_embeddings_into` = f32 LE: none -> tokens x n_embd,
  rank -> n_cls_out scores, else one n_embd vector. `request_rerank_tokenize(r,
  query_len)` mirrors llama.cpp server `format_prompt_rerank`.
  `request_tokens_set(r, i32le_ids)` feeds raw ids (vocoder codes), checked
  against the vocab. `request_sampler_configure(r, temp_milli, top_k,
  top_p_milli, repeat_milli, seed)`; greedy stays the default.
- **Verified (release seed `C:/dev/seeds/simple-release.exe`, CPU shim):**
  Qwen2.5-1.5B chat + bge-small-en-v1.5 q8_0 + bge-reranker-v2-m3 Q8_0 resident
  in one process; cos(cat,kitten)=0.789 vs cos(cat,stock)=0.331; rerank Paris
  doc 7.78 vs Berlin -5.45, bananas -11.04; pooling none on 4 raw ids = 1536
  floats (4 x 384). Trap: under the release seed a RELATIVE `SLANG_GGML_LIB`
  failed `open_backend`; pass an absolute path.

### Serving: /v1/embeddings and /v1/rerank (L4)

- `model_executor/runners/pooling_runner.spl` (`pooling_runner_open/run/close`)
  opens the shim itself and loads the model as a HANDLE, so a resident chat
  model is never evicted; `release_backend_library` drops the dlopen ref
  without `slang_ggml_free`. One request per input, n_ctx 2048.
- `entrypoints/openai/serving/serving_pooling.spl`: embeddings = OpenAI list
  shape, L2-normalized, `encoding_format` float|base64 (normalized f32 LE);
  rerank = `{query, documents, top_n}` -> `results[{index, relevance_score}]`
  sorted, score = sigmoid(logit). String inputs only (token-id input -> 400).
- `bge-reranker-v2-m3` GGUF (gpustack Q8_0) has NO `bert.pooling_type` key; the
  resolver reaches Rerank from its `cls.output.weight` tensor (a pre-review L1
  that stopped at the tokenizer block said Embedding).
- Traps: `env_get` answers "" (not nil) when unset, so `?? default` never
  fires; `protocol.json_int_field` fails on the release seed (`ord` not
  found), so top_n is read from the parsed tree; a private `_sigmoid` helper
  returned ~1e-19 (bug `slang_serving_pooling_sigmoid_helper_wrong_value_2026-11-19.md`).
- `generate_on_request(BackendActiveGenerationRequest)` generates on a
  caller-opened request (e.g. `open_request_for`), used by L5 TTS.
- Live: `test/03_system/lib/slang/feature/slang_pooling_live_spec.spl` 5/5 on
  the CPU shim and on the Vulkan shim (13/13 layers on the Radeon 8065S).

## TTS / speech (L5, live-verified 2026-11-19, Windows CPU shim)

- Pipeline: `serving/serving_speech.spl` -> `runners/tts_runner.spl`
  (`tts_open` / `tts_run` / `tts_close`) -> `runners/istft.spl` -> wav. Model
  dir = OuteTTS GGUF + WavTokenizer GGUF + `slang_kind.sdn`
  (`kind: tts`, `vocoder: WavTokenizer-Large-75-F16.gguf`); C:/dev/model has
  `OuteTTS-0.2-500M-GGUF` (OuteAI Q8_0 + ggml-org WavTokenizer F16).
- `tts_open` loads both GGUFs as L4 model handles (`open_model_handle`) BESIDE
  any chat model; `tts_close` closes only the handles and dlcloses its own
  library reference. Never `close_backend` there: it frees the chat engine's
  global model. `serve_speech` opens per request and closes after it.
- Stage 1: OuteTTS-0.2 prompt = `<|im_start|>\n` + en_male_1 speaker words +
  `outetts_process_text(input)` (numbers to words, a-z only, `<|text_sep|>`)
  + `<|text_end|>\n` + speaker audio block (ported from llama.cpp tts.cpp
  67b2b7f2f2d; the local rev 99b9548 tts.cpp is the generic mtmd tool).
  Generated on a handle request via `backend.generate_on_request`. Sampler
  default = tts.cpp's top-k 4, temp 0.8, seed 42 (`tts_set_sampler`).
- Trap (fixed by L4 cdaba0b8b52, `slang_ggml_request_is_eog`): before it, EOG
  never fired on a model-handle request (is_eog read the default model's
  vocab), so generation ran to its cap and
  OuteTTS invented more words (run 1: 2048 tokens, 13.3 s, ASR heard extra).
  `outetts_spoken_codes` keeps codes up to `<|audio_end|>` and only for the
  input's word count (safety net). Budget 128 + 64 tokens/word, n_ctx 8192,
  input <= 100 words (400 `input_too_long`); an over-budget prompt is refused.
- Stage 2: codes (< 4096) -> `request_set_tokens` on the vocoder handle,
  `request_embed_configure(POOLING_NONE)`, `request_embeddings` = n_codes x
  1282 f32 rows `[ln|X| | phase]`. L4's `embed_eval` uses llama_decode and it
  works for wavtokenizer-dec.
- ISTFT: n_fft 1280 / hop 320, mag clamp 100, periodic Hann, OLA /
  sum(hann^2), centre crop; irfft is the exact Hermitian inverse via
  mixed-radix FFT. First 0.25 s zeroed as in tts.cpp.
- Live (`test/03_system/lib/slang/feature/slang_tts_live_spec.spl`, release
  seed, CPU shim): "The capital of France is Paris." -> 2.1 s wav -> Qwen3-ASR
  chat media -> `The capital of France is Paris.` (top-k and greedy both).
  Run 5 (L4 shim cdaba0b8b52, EOG works): prompt 901 tokens, 194 generated
  (cap 512), TTS wall 174 s = generate 4.9 s + vocoder 32 s + ISTFT+wav 128 s;
  ASR 110 s. Before the EOG fix: generate 16 s (976 tokens), ISTFT+wav
  117-123 s for ~155 frames. Under `run` the same ISTFT is ~42 ms/frame
  (200 frames 8.4 s): ~770 vs ~42 ms/frame, cause not isolated
  (`doc/08_tracking/bug/slang_tts_istft_vocoder_decode_slow_in_spec_2026-11-19.md`).
- Unit specs: `model_executor/istft_spec.spl` (hand irfft values, naive-sum
  cross-check, STFT round trip), `model_executor/tts_prompt_spec.spl`,
  `entrypoints/serving_speech_spec.spl` (validation: `input` <= 4096 chars,
  only `wav`, else 400 `unsupported_response_format`; base64 JSON envelope
  `object: audio.speech` until L2's binary body).
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

## ASR / `/v1/audio/transcriptions` (lane L3, 2026-11-17)

`serving/serving_transcriptions.spl`: `serve_transcriptions(model_root, body)`, body JSON `{model, file_b64, format[, max_tokens]}` (multipart waits for L2). It does NOT use `model_for_kind(Asr)`: Qwen3-ASR resolves as Chat [Text, Audio], so the handler accepts a Chat model with Audio input (recording as the only user content through `engine_complete_chat_media`, `language X<asr_text>` prefix stripped by `strip_asr_prefix`) or an Asr model through the whisper runner, and answers other models 400 `wrong_model_kind`. Phase A live (Qwen3-ASR-0.6B Q8_0, jfk.wav, CPU, model load included): "And so, my fellow Americans, ask not what your country can do for you; ask what you can do for your country." in 129 s. Specs: `test/01_unit/lib/gc_async_mut/slang/serving/serving_transcriptions_spec.spl`, `test/03_system/lib/slang/feature/slang_asr_live_spec.spl` (needs an mtmd shim: `SLANG_SHIM_MTMD=1`).

### ASR phase B: whisper.cpp (2026-11-18)

`model_executor/runners/whisper_runner.spl` (`whisper_available/open/run/close`; library path ONLY from `SLANG_WHISPER_LIB`, dlopened only in `whisper_open`) over `src/runtime/slang_whisper_shim.c` (`slang_whisper_{abi,init,transcribe,text_into,free}`, int64 ABI: model path and s16le PCM go in with `spl_wffi_call_i64_with_bytes`, transcript comes out with `spl_wffi_call_i64_into_bytes`). Build: `SLANG_SHIM_OUT_DIR=<dir> sh scripts/check/build-slang-whisper-shim.shs` (llvm-mingw only; whisper.cpp from `C:/dev/tools/whisper.cpp` built `BUILD_SHARED_LIBS=OFF` so ggml is inside the DLL; the script fails if the DLL imports a `ggml*.dll`). Model `C:/dev/model/whisper-tiny.en/ggml-tiny.en.bin` (HF `ggerganov/whisper.cpp`, 77.7 MB, `lmgg` magic -> kind Asr). Only 16 kHz wav is accepted (other rates -> 400 `invalid_media` with the reason; no resampling). Live (CPU, jfk.wav): "And so my fellow Americans ask not what your country can do for you ask what you can do for your country." in ~30-32 s per request, the same on the second call, so model load is not the cost: the pure-Simple wav decode + s16 packing of 176k samples dominates.

## Image generation: /v1/images/generations (L6, 2026-11-17)

- `serving/serving_images.spl` -> `model_executor/runners/sd_runner.spl`
  (`sd_runner_open/run/close`; deliberately NOT wired into `kind_dispatch.kind_open`,
  which would load a multi-GB model just to answer a 501) -> `src/runtime/slang_sd_shim.c` (stable-diffusion.cpp
  opaque-options C API, **ggml statically linked** into `slang_sd.dll`).
- Body `{model, prompt, n<=4, size, response_format:"b64_json", steps, seed}`;
  reply `{created, data:[{b64_json}]}` (PNG via `common/image/png_encode.spl`,
  stored deflate). `url` format = 400. `size` = WIDTHxHEIGHT, both multiples of
  64, <= 768, default 512x512; defaults steps 4 (1..50), n 1..4, negative/absent seed = random (cfg 1.0, sd-turbo).
  Every field is validated (400) before the runner is touched; a wrong JSON type
  (`"size":512`, `"response_format":5`) is 400, JSON null = absent. One generation at a
  time: `sd_runner_try_acquire` (AtomicBool) gates open/run/close, a concurrent request
  gets 503 `busy`; `defer sd_runner_release()` frees it on every return path (not on a
  panic: `doc/08_tracking/bug/slang_sd_busy_flag_not_released_on_panic_2026-11-22.md`). `created` is unix seconds.
  No `SLANG_SD_LIB` / missing DLL = 503 `runner_unavailable`; wrong kind = 400.
- Build: `sh scripts/check/build-slang-sd-shim.shs` (CPU,
  `build/sffi/sd-cpu/slang_sd.dll`) and `SLANG_SD_VARIANT=vulkan
  SD_VULKAN_SDK_DIR=... VULKAN_GLSLC=... sh ...` (`sd-vulkan/`). Needs
  stable-diffusion.cpp at `SD_ROOT` (default `/c/dev/tools/stable-diffusion.cpp`),
  llvm-mingw clang, cmake, ninja. Vulkan needs `-DSPIRV-Headers_DIR` (the script
  derives it from the SDK dir). The runtime DLLs are copied beside the shim.
- Model: `stabilityai/sd-turbo` `sd_turbo.safetensors` (5.2 GB, fp32 all-in-one)
  in `C:/dev/model/sd-turbo/`; the resolver sniffs `model.diffusion_model.`.
- ABI: prompt/path in via `spl_wffi_call_i64_with_bytes`, RGB8 out via
  `spl_wffi_call_i64_into_bytes`; the zero buffer and ARGB conversion are local
  loops (replace with L2's `bytes_zeroed`).
- Specs: `test/01_unit/lib/gc_async_mut/slang/sd_runner_spec.spl` (no model),
  `test/03_system/lib/slang/feature/slang_sd_image_live_spec.spl` (live, env
  `SLANG_LIVE=1 SLANG_MODEL_ROOT SLANG_SD_LIB SLANG_SD_STEPS SLANG_SD_SIZE`).
- Needs ~10 GiB free for the load; run one image at a time.
- Host access in the runner goes through `host/slang_host` (`host_env`, `host_file_exists`).

## Post-merge review follow-ups (#10682, 2026-11-22)
- **Video input:**
  - ffmpeg output is capped at 16 MiB, the hard cap of `rt_process_run_bounded_bytes`; a larger cap never spawns ffmpeg.
  - One video part per request (400 `too_many_video_parts`). The check runs before expansion; `video_frames_spec` pins it through `/v1/chat/completions`.
  - Server faults return 503 `video_sampling_failed`.
  - ffmpeg runs with `-protocol_whitelist file`, and the request is refused when no temp directory is set.
- **Images:**
  - A single owner behind an atomic busy flag; a concurrent request gets 503 `busy`.
  - `n` is 1..4 and `steps` 1..50, checked before the model loads.
- **Tree KV:** the live spec reads `n_ubatch` from `engine_tree_cache_stats`. Measured on Vulkan:
  - Roughly half the prefill and 1.6-1.8x faster. Qwen2.5-1.5B digests match, but every logits step differs at bit level, so that match is greedy luck.
  - Mode 3 is not bit-exact against cache-off on Vulkan for any model: ggml-vulkan fusion skips the multi-stream KV write, and stale data in freed KV cells changes flash-attention output. Gemma branching is where argmax flips (live spec 2/3). See `doc/08_tracking/bug/slang_tree_kv_gemma_branching_digest_differs_on_vulkan_2026-11-22.md`.

## L4 + L5 landed together (2026-11-22)
- **Every kind route is served now:**
  - chat and multimodal through `llm_engine`;
  - asr through `whisper_runner` or an audio chat model;
  - image generation through `sd_runner`;
  - embeddings and rerank through `pooling_runner_serve`;
  - tts through `tts_runner`.
- The 501 stub `kind_not_implemented_response` and `engine/kind_dispatch.spl` were deleted; nothing reached them any more. Earlier mentions of `kind_dispatch.kind_open` above are history.
- `pooling_runner_serve` is stateless. Each request opens the shim library and a model handle and closes both before returning. Module state is thread-local under the interpreter, so a cached handle would leak a shim model slot on every connection thread.

## Review follow-ups (2026-11-23)
- Request JSON string readers (`json_string_field`, `json_stop_sequences`) share one decoder that now handles `\uXXXX`, surrogate pairs (lone surrogate -> U+FFFD) and passes a malformed escape through. Spec: `protocol_json_unicode_spec.spl`.
- `pooling_runner` refuses an embedding request on a model whose effective pooling is none (it would return one vector per token as if it were one input); the vocoder path still asks for pooling none explicitly.
- The shim refuses `embed_eval`, `rerank_tokenize` and `tokens_set` on a tree request (shared tree context / leased token path). Test: `tree_cache_test.c` with `mock_llama_memory_clears`.
- `tts_runner` releases the shim library through `release_backend_library` instead of its own `spl_dlclose` import.
- `skip()` inside an `it` body is counted as skipped by `spec.spl` (`_execute_it` returns "skip", `test_skipped` rises), not as a pass. This holds on the self-hosted and aggregate path only; the seed's native `it` (bdd.rs) still reports a pass, so live specs keep the explicit `SKIPPED:` line. Pinned by `test/01_unit/lib/nogc_sync_mut/spec_skip_in_body_spec.spl`.

## Pure-runner model directory and float bit helpers (2026-11-23)

- Pure-runner specs and `stories15m_generate.spl` resolve the stories15M directory through `test/fixtures/slang_pure/model_dir.spl`: `SLANG_PURE_MODEL`, else `llama2c-stories15M` under `SLANG_MODEL_ROOT`; no built-in default path.
- `std.common.binary_io` exports `f32_from_bits`, `f32_to_bits`, `f64_from_bits`, `f64_to_bits`; `std.gc_async_mut.binary_io` imports them instead of keeping a private copy (the copy turned NaN into 0.0 and lost -0.0).
