# Browser timer clock snapshot

The browser host samples its SOSIX/host clock once per scheduling turn and
injects that value as `BrowserClockSnapshot`. Timer deadlines and animation
frame boundaries are derived from that immutable value; callback dispatch does
not read time, environment variables, or process state.

The explicit `set_timeout_at`, `set_interval_at`, and
`request_animation_frame_at` APIs are the preferred host boundary. Existing
JS-transpiled calls keep using `set_timeout`, `set_interval`, and
`request_animation_frame`; those compatibility façades consume the last clock
snapshot published to their canonical `EventLoop`.
Before a positive snapshot exists, scheduling fails closed instead of creating
an epoch-zero deadline. Signed-microsecond overflow is rejected before queue
mutation.

The focused scenarios prove absolute deadline preservation, compatibility
behavior, shared-snapshot interval/rAF scheduling, missing-clock rejection,
and deadline-overflow rejection.
