# JavaScript Timer Resource-Limit Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 5 | 5 | 0 | 0 |

## Scenarios

- A long-overdue interval fires once per monotonic clock advance instead of
  replaying every missed millisecond.
- Nested zero-delay scheduling yields after 1000 callbacks in one drain.
- An interval can cancel its already queued continuation from its callback.
- A document retains at most 4096 pending timer tasks; additional concurrent
  schedules return `undefined`.
- A single self-rescheduling `requestAnimationFrame` chain remains live beyond
  4096 historical handles.

Requirement trace: REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-017,
REQ-WEB-BROWSER-018.

Source: `test/01_unit/lib/common/js_timer_drain_limit_spec.spl`

Updated: 2026-07-26.
