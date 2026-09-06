# Caret cannot yet launch Slang local inference

## Status

**Partly resolved 2026-09-04.** Caret now runs a local model through slang and
gets real tokens back. The gate row `caret-local-llm-launch` in
`config/check/must_check_gates.sdn` is **deliberately left as a non-passing
bootstrap TODO** -- see "Why the gate is not promoted" below. Do not promote it
on the strength of this record.

## What the 2026-08-21 evidence said, and what is true now

Each original bullet, corrected:

- ~~"`src/lib/gc_async_mut/slang/` supplies tensor-pack loading and streaming
  readiness, but no token-generation request/response endpoint."~~
  **Now false.** `src/lib/gc_async_mut/slang/engine/llm_engine.spl` holds a
  resident model and generates; `entrypoints/llm.spl` is the in-process
  request/response surface (mirroring `vllm/entrypoints/llm.py`), and
  `entrypoints/openai/serving_chat.spl` is the HTTP one.

- ~~"`src/app/llm_caret/provider.spl` dispatches `local_torch`; it has no
  `slang` provider."~~
  **Was already stale when written, and is doubly so now.** A `slang` provider
  (OpenAI-compatible HTTP) existed; a second provider, `slang_local`, now runs
  slang in-process with no socket. They differ in transport, not in engine, and
  both report which one answered.

- "`check-caret-suite-bootstrap.shs --gate local-torch` checks the independent
  Python/Torch provider and is therefore not Slang launch evidence."
  **Still true**, and still the reason that gate proves nothing about slang.
  The new evidence is `scripts/check/check-slang-ggml-inference.shs`, which
  drives caret itself.

## What was actually done

slang owns the loading, the residency decision, the memory admission and the
decode loop; ggml supplies the kernels pure Simple does not have yet
(dequantization of Q4_K_M, attention, the tokenizer). This is the same division
vLLM makes when it drives cuBLAS/FlashAttention rather than writing GEMMs. The
boundary is `src/runtime/slang_ggml_shim.c` (int64-only ABI, reached through the
dynamic SFFI) behind `model_executor/backend.spl`.

Measured 2026-09-04 on a DGX Spark (GB10, aarch64, 128 GB unified), through
`caret --provider slang_local`:

```
MODEL Qwen3-Coder-Next-Q4_K_M -> GENERATED: A compiler is a software tool that
  translates source code written in a high-level programming language into
  machine code ... that a computer's processor can execute directly.
```

## Why the gate is not promoted

The unblock condition in the original record is a specific bar, and two parts of
it are unmet:

1. **"launch the local service ... and stop the service without leaked child
   processes."** The run above has no service to launch: it is in-process,
   because slang's HTTP surface is currently unreachable on the bootstrap seed
   for two reasons that are not slang's --
   `seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md` and
   `seed_http_server_handle_connection_dispatch_2026-09-04.md`. Until a
   pure-Simple `bin/simple` serves that request, the service half of the bar is
   untested.

2. **A native slang executor still does not exist.** Master plan phases A3
   (streaming loader) and A4 (paged KV cache + paged attention) are absent, so a
   slang *pack* remains unrunnable and `/v1/chat/completions` still answers 503
   with `"stub":true` for one. What runs today is GGUF through ggml.

## What would close this

- A pure-Simple `bin/simple` running
  `scripts/check/check-slang-ggml-inference.shs` green, plus the same check
  extended to start `src/app/slang_server/main.spl`, drive
  `caret --provider slang` (the HTTP one) against it, and stop it with no leaked
  children.
- Then, separately, A3/A4 for the native path, at which point the `"stub":true`
  branch in `serving_chat.spl` stops being reachable for a slang pack.
