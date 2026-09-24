# Feature expert: slang local inference

**Feature:** running a local LLM through slang, and reaching it from caret.
**Last updated:** 2026-09-04

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

## Things that will bite you

- **The seam is drawn at the decode loop, on purpose.** `generate` in
  `backend.spl` steps one token at a time so KV positions, stop conditions and
  the token budget stay in Simple. If you move the loop into C to make it
  faster, slang stops owning the thing that makes it slang.
- **Clear the KV cache between requests.** The model stays resident; the
  conversation must not. `generate` calls `slang_ggml_kv_clear` first. Without
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

## Current limits

- GGUF only. safetensors (BF16, NVFP4) is recognised and refused.
- One model, one context, greedy sampling, one request at a time.
- No continuous batching or prefix caching — that is master plan A5, and it
  needs the A4 paged KV cache underneath it.
- The HTTP path is unreachable on the bootstrap seed; see
  `doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md`
  and `doc/08_tracking/bug/seed_http_server_handle_connection_dispatch_2026-09-04.md`.

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

## Related

`doc/05_design/ml/slang/slang_master_plan.md`,
`doc/07_guide/app/llm/local_llm_slang_caret_setup.md`,
`doc/08_tracking/bug/caret_slang_local_inference_provider_missing_2026-08-21.md`.
