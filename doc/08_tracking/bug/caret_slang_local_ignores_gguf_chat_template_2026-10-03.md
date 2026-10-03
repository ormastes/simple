# caret slang_local ignores the model's GGUF chat template (2026-10-03)

**Status:** open.

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
