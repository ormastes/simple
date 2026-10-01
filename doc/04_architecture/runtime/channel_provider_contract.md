# Channel Provider Contract

The common lifecycle is finite admission, FIFO drain, explicit close, explicit
free, and stale-handle rejection. Capacity is 1024. Send returns accepted or
rejected; full and closed are ordinary rejection for a live scalar handle.
Close rejects later sends while preserving queued FIFO values. Empty,
closed-and-drained, timeout, invalid, and stale typed-scalar receive all return
the scalar sentinel `0`; callers needing those states distinguished must carry
an outer lifecycle/status envelope. `try_recv` never blocks. Blocking receive
wakes on send, close, or free. Free retires the generation and waits for
admitted native operations before slot reuse.

The C `rt_channel_*_i64` API admits signed values representable by Simple's
tagged integer (`[-2^60, 2^60-1]`). Its legacy `Any` entry admits only classified
inline scalar words. The interpreter typed-scalar adapter accepts only
`Value::Int` within that exact closed interval and uses the same
capacity/send/close/drain/sentinel contract. Both endpoints round-trip
unchanged; `-2^60-1` and `2^60` reject before provider dispatch. Malformed calls
are interpreter errors rather than native memory values. Receive performs no
arithmetic conversion: admitted `Value::Int` is returned unchanged, while a
non-integer or absence maps to the `0` sentinel.

Rust `ChannelProvider` is an in-process object channel, not the scalar ABI. It
shares capacity, FIFO, backpressure, close/drain/free, and nonblocking-empty
semantics, but admits recursively immutable `Value` objects and reports invalid
or stale handles as `CompileError`. Mutable dynamic descendants reject before
admission. No timeout method exists on `ChannelProvider`; watchdog polling in
the interpreter blocking receive is execution control, not a channel outcome.

## Focused evidence (2026-08-12)

`scripts/check/check-runtime-native-channel-lifecycle.shs` produced
`runtime-native-channel-lifecycle: PASS` for the direct C contract probe. The
combined run then stopped compiling the Rust test on a test-only ambiguous
string conversion, before Rust execution. That conversion was corrected, but
the bounded suite was not rerun. C runtime evidence is PASS; interpreter and
Rust object-provider execution remain HOLD.

The scalar-range correction added exact endpoint and adjacent-rejection tests.
Its isolated targeted Cargo run compiled dependencies and reached the
`simple-compiler` final build, then produced no progress for several minutes;
it was interrupted under the repository runaway guard. No scalar-test PASS is
claimed from that run.
