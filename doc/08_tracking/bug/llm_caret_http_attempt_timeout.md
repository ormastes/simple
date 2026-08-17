# LLM Caret HTTP Attempt Timeout

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Status

Open runtime/API limitation.

## Problem

`src/app/llm_caret/retry.spl` enforces its total retry deadline before and
after each synchronous callback and before every retry sleep. The underlying
`http_request_raw` API has no timeout/cancellation parameter, so a transport
call blocked inside the runtime cannot be interrupted by `with_retry`.

## Required fix

Add a timeout-capable HTTP facade/runtime operation, pass the remaining retry
budget into every Claude/OpenAI-compatible request, cancel the transport when
the deadline expires, and verify elapsed time plus resource cleanup with a
local server that intentionally never completes a response.

## Acceptance evidence

- a hung attempt returns a timeout outcome within the configured tolerance;
- late successful responses are rejected after the deadline;
- no retry sleep exceeds the remaining budget;
- sockets/tasks are released after cancellation;
- Claude API, OpenAI, and compatibility-provider system specs use the same
  timeout-capable facade.

## Verification 2026-08-17 (content classification) — LIVE

`src/lib/nogc_sync_mut/io/http_sffi.spl:184` still reads:

    fn http_request_raw(method: text, url: text, headers_text: text, body: text) -> (i64, text, text)

No timeout parameter, and the body delegates straight to `rt_http_request(method,
url, headers, body)` (line 188), which takes no deadline either. So `with_retry`
still cannot cancel a blocked transport — a stalled socket hangs the attempt
rather than failing it.

Fix is not containable in `src/lib/**`: the deadline has to reach the
`rt_http_request` extern, i.e. the Rust/C runtime, before the Simple-side
signature is worth widening. Recorded, not patched.

Not proven: no `Results:` line — no reproduction harness exists for a stalled
transport.
