# LLM Caret HTTP Attempt Timeout

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
