# slang server: /v1/chat/completions usage counts are always 0

- Date: 2026-11-15
- Severity: P3 (wrong metadata; completion text is correct)
- Status: open (filed, not fixed)
- Host: Windows 11, CPU ggml shim, Qwen2.5-1.5B-Instruct-Q4_K_M

## Symptom
Live run of `test/03_system/lib/slang/feature/slang_http_server_live_spec.spl` (log
`build/probe/http_gated.log`): a real completion returns
`"usage":{"prompt_tokens":0,"completion_tokens":0,"total_tokens":0}` for every request.

## Cause
`src/lib/gc_async_mut/slang/entrypoints/openai/serving_chat.spl:110` hard-codes
`openai_chat_completion_response(request.model, content, 0, 0)`. `engine_complete_chat`
(`src/lib/gc_async_mut/slang/engine/llm_engine.spl:368`) returns only the text, so the
token counts are not available at the call site.

## Fix direction
Return prompt/completion token counts from the engine (the backend already tracks
`tokens_prefilled`) and pass them through. The live spec currently pins only that the
usage keys exist; tighten it to `total_tokens > 0` with the fix.
