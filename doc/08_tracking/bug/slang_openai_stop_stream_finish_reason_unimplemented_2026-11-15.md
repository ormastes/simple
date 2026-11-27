# slang server: finish_reason, `stop`, `stream:true` are not implemented

- Date: 2026-11-15
- Severity: P2 (OpenAI clients rely on all three)
- Status: FIXED 2026-11-16 (see "Resolution" below); cases moved into `slang_openai_conformance_live_spec.spl`
- Host: Windows 11, CPU ggml shim, Qwen2.5-1.5B-Instruct-Q4_K_M, server on port 47732

## Observed (log `build/probe/conf_dev.log`)
1. `max_tokens: 1` -> HTTP 200, `"content":"The"`, `"finish_reason":"stop"`. Expected `length`.
   `finish_reason` is hard-coded in `protocol.spl` `openai_chat_completion_response`; the engine
   (`engine_complete_chat`) returns only text, so neither the stop cause nor a token count reaches
   the handler.
2. `stop: [","]` with "Count from 1 to 5 separated by commas" -> 200,
   `"content":"1, 2, 3, 4, 5"`. Expected content without a comma and `finish_reason` stop. `stop`
   is never parsed (`parse_chat_request` keeps only model, messages, max_tokens, stream).
3. `stream: true` -> `HTTP/1.1 400 Bad Request` (`streaming is not supported by this slang
   build; send stream=false`, `protocol.spl` `parse_chat_request`). `main.spl` builds every
   response through `HttpResponse` with a complete body, so SSE would also need a chunked/streaming
   writer in the HTTP server and a per-token callback from `llm_engine.spl`.

`temperature`, `top_p`, `seed`, `n` are likewise ignored (greedy decoding).

## Fix direction
Have the engine return `{text, prompt_tokens, completion_tokens, stopped_by_eos}` (same change that
fixes `slang_openai_usage_counts_always_zero_2026-11-15.md`), derive `finish_reason` from it, apply
`stop` by truncating the stream of decoded text, then add an incremental generate API for SSE.
`serving_chat.spl` usage code and `engine/llm_engine.spl` were being edited by another agent when
this was filed, so nothing was changed there.

## Resolution (2026-11-16)
All three gaps closed on the ggml lane; no C shim change was needed because slang's own decode loop
(`backend.spl`) already samples one token at a time.
- `finish_reason`: `GenStream`/`gen_stream_step` report "length" when the token budget ended generation and
  "stop" for an end-of-generation token or a stop sequence; carried through `BackendGeneration` and
  `EngineChatResult` into both response envelopes.
- `stop`: parsed as string or array (`json_stop_sequences`), applied per token with `stop_scan` (partial matches
  are held back), pure runner applies it to its finished text.
- `stream:true`: `serving_stream.spl` + `SimpleHttpServer.with_stream_handler` write SSE frames to the socket as
  tokens are produced (chat and completions). Live cases 2, 3, 3b, 5, 5b in
  `slang_openai_conformance_live_spec.spl`.
Remaining gaps: the pure runner and a shared-context backend stream as one content frame (valid SSE, not
incremental); image/audio requests with `stream:true` get 400 `unsupported_modality`; `usage` is not sent in
stream frames; sampling params (`temperature`, `top_p`, `seed`, `n`) are still ignored.
