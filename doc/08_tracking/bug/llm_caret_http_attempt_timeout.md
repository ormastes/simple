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

## Addendum 2026-11-11 — lane p3-caret2: seed-side classification gap closed;
## live gate now fully green on the tracked seed

Traversed on work/p3-caret2-20261111 (origin/release/1.0.0 tip
66506fda143ca).

- The residual gap was pure error-text classification: the seed transport
  surfaces the raw Windows WSAETIMEDOUT ("os error 10060") for a deadline
  expiry, while the self-hosted runtime classifies the same condition as
  "HTTP request timed out" (src/runtime/runtime_native.c) — the text the
  live gate's spec asserts.
- Seed-side workaround applied (this lane): the typed boundary
  `http_request_v2_raw` in src/lib/nogc_sync_mut/io/http_client_core.spl now
  normalizes known timeout transport errors (timed out / timeout /
  WSAETIMEDOUT / ETIMEDOUT / os error 10060 / deadline exceeded) to the
  self-hosted classification "HTTP request timed out". Non-timeout errors
  pass through unchanged; the negative-timeout preflight is untouched. This
  mirrors the app-layer classification precedent in multimodal_provider.spl
  and makes the facade's failure text identical across engines.
- Live verification on the tracked seed (Windows):
  `python scripts/check/check-caret-http-attempt-timeout.py --runtime
  bin/simple.exe` — exit 0; the spec runs 5/5 PASS (three stalled adapters
  interrupted within the 100 ms budget and tolerance, UTF8 echo round-trip,
  negative timeout rejected before any request) and the server ledger
  assertion holds ({"/slow": 3, "/echo": 1} — exactly three bounded
  attempts, no negative-timeout request) (log:
  build/review/p3fix-caret2-20261111-logs/t4_http_gate.log). Unit regression
  retry_timeout_spec stays 4/4 (log: t4_retry_unit.log).

The gate's designed target remains a qualified self-hosted POSIX runtime;
with the cross-engine classification bridge the same check now also passes
end to end on the tracked seed, closing the seed-runnable half of the row.
