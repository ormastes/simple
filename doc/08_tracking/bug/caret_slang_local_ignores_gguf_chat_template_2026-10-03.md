# caret slang_local ignores the model's GGUF chat template (2026-10-03)

**Status:** caret side fixed 2026-11-16 (see Update); engine admission part open.

## Symptom
`caret --provider slang_local --model Qwen2.5-0.5B-Instruct-GGUF --prompt
"Say exactly: hello"` loads the model and generates, but the reply is a code
fence or a `[Think]` loop to the token cap — never "hello". The 1.5B model of
the same family answers correctly. Given its own ChatML template directly, the
0.5B model replies "Hello! How can I assist you today?".

## Cause
`src/app/llm_caret/main.spl` `_render_agent_transcript` flattens the
conversation as raw `role: content` lines plus a `assistant: <think>` prefill
tuned for Qwen3.5 raw completion. Smaller instruct models only follow their
trained template (`tokenizer.chat_template` in the GGUF metadata).

## Fix direction
Have the slang engine apply the GGUF's own chat template (or a per-family
template table keyed by `general.architecture`) instead of caret hard-coding a
transcript format. Must be re-verified on the Qwen3 / Qwen3-Coder hosts the
current format was tuned on before changing the default.

## Related cost (not a defect, recorded per the perf rule)
On Windows the slang memory gate reads free RAM through PowerShell CIM
(`memory_budget.spl` `_win32_os_kib`), ~1.2 s per probe and two probes per
model load (~2.4 s added to every load).

## Evidence
`test/03_system/app/llm_caret/caret_slang_local_hello_system_spec.spl`:
green with the 1.5B model; with `CARET_SLANG_MODEL=Qwen2.5-0.5B-Instruct-GGUF`
the hello scenario fails (`expected ``` to contain hello`).

## Update 2026-11-16 (caret hello spec 930 s outer bound, 0 passed)
Root cause of the ~145 fabricated "Assistant:" turns: `main_responder`
(`src/app/llm_caret/main.spl`) sent slang_local the flat transcript from
`_render_agent_transcript` through `slang_generate` -> `engine_complete` ->
`engine_generate_observed_request` (`llm_engine.spl:375-376`, `chat: false`), so
the model never saw its chat template, never emitted `<|im_end|>`, and kept
role-playing "user:/assistant:" until the 2048-token cap
(`provider.spl` `_dispatch_slang_local`). End-of-generation tokens ARE honored
by the shim (`slang_ggml_is_eog`, `slang_ggml_shim.c:825,1180,1190`).
Fix: slang_local now uses `engine_complete_chat` (chat frames, template + EOG)
via `slang_generate_chat` (`entrypoints/llm.spl`) and `dispatch_slang_local_chat`.

Open, in a file owned by another lane: `llm_engine.spl:223-224`
`_runtime_overhead_bytes()` is a flat 6 GiB regardless of n_ctx, so admission
demands 10 GiB (1 weights + 6 + 3 headroom) even for the 1.5B model and refuses
to load when other processes hold RAM ("refusing to load ... only N GiB
available", measured 2026-11-16 with 1-5 GiB free). Fix: make it proportional to
`ENGINE_N_CTX` (KV bytes ~ n_ctx * n_layer * 2 * n_embd_kv * 2, or a per-token
figure) so a 4096-token context asks for well under 1 GiB; caret can then size
n_ctx to the request (it passes a fixed 32768, `provider.spl`).
