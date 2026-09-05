# JavaScript Promise Microtask Resource-Limit Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

- Promise draining yields after 1000 callbacks without discarding remaining
  microtasks.
- A document retains at most 4096 pending Promise handlers.
- Settled Promise reactions remain deferred until a microtask drain, then
  release their handler and registration records.

Requirement trace: REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-017,
REQ-WEB-BROWSER-018.

Source: `test/01_unit/lib/common/js_promise_microtask_limit_spec.spl`

Updated: 2026-07-26.
