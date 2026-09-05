# Frame pacing through the SOSIX host timer

The compositor frame pacer computes timing policy but does not sleep through a
runtime or platform primitive. The WM supplies one monotonic clock sample and
an opaque timer capability; the pacer returns a typed `SosixTimerRequest` with
an absolute nanosecond deadline.

## Operator-visible contract

- A 60 Hz frame starting at 100 ms and sampled at 104 ms has 12 ms remaining.
- With `now_ns = 1,000,000,000`, the requested deadline is
  `1,012,000,000` ns.
- A timer capability with generation zero is rejected as `invalid-timer`.
- When the budget is already consumed, the deadline equals `now_ns`; the
  migration does not add a one-millisecond sleep the former path skipped.
- Rejection does not fall back to a direct sleep, environment read, process,
  display adapter, or renderer path.

Rendering ownership is unchanged: GUI and web content continue through
`DrawIrComposition` and Engine2D. Engine3D remains a separate consumer lane.
