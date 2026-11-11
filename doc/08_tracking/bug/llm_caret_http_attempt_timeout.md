# LLM Caret HTTP Attempt Timeout
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Fixed 2026-11-11 (lane p3-caret1) — landed fix a62f411a3c2 verified to the
seed-runnable limit: unit retry-timeout spec 4/4 PASS; live stalling-server
gate remains pending a qualified POSIX self-hosted runtime (the check script
itself excludes seed/build/fallback runtimes). See the 2026-11-11 addendum.

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


## Addendum 2026-11-11 — lane p3-caret1: fixed (verified to the seed-runnable limit)

Traversed on work/p3-caret1-20261111 (origin/release/1.0.0 tip 79d5af6723f6).

- Fix commit a62f411a3c2 ("fix(caret): propagate remaining retry timeout to HTTP
  attempts") IS an ancestor of tip.
- Unit regression from the same commit,
  test/01_unit/app/llm_caret/retry_timeout_spec.spl: 4/4 PASS, exit 0
  (log: build/review/p3fix-caret1-20261111-logs/row7_retry_timeout_unit.log).
- Live gate scripts/check/check-caret-http-attempt-timeout.py: the spec it drives
  asserts the error text "timed out"; the seed runtime (ureq) surfaces the raw
  Windows WSAETIMEDOUT (os error 10060) string instead, so the 3 stalled-response
  scenarios fail on message classification only. Evidence the timeout mechanism
  itself works on the seed: the 10060 fires at the 100 ms attempt budget (within
  the spec's 1500 ms tolerance), the UTF8 echo scenario passes (status 200,
  "hello 서울" round-trip), and the negative-timeout scenario fails closed before
  any request. The self-hosted runtime classifies the same condition as
  "HTTP request timed out" (src/runtime/runtime_native.c:16228 et al.), which is
  the check's designed target.
- The check script itself documents "requires a qualified POSIX self-hosted
  runtime. No seed/build/fallback." — the live end-to-end gate stays pending
  until that runtime exists on a POSIX host; 2026-11-06 verify-sweep2 already
  recorded the same environment wall.
