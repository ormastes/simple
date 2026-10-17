# SMUX bounded input queue ownership

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/01_unit/os/apps/smux/input_queue_spec.spl`.
Requirement: **REQ-SMUX-INPUT-001** — all 12 executable scenarios carry this trace.
No admitted general SSpec runtime is available; none of these 12 scenarios has
executed. This manual records expected behavior, not a passing transcript.

The production `PaneInput` value stores original text, cached UTF-8 bytes, a
byte offset and a deferred error. The sole service owner advances this value
after provider acceptance. Queue acceptance does not prove child delivery.

1. Create an empty queue. Original text, byte storage and offset are empty;
   there is no deferred error.
2. Enqueue `é`, accept only its leading byte and inspect the remaining raw
   continuation byte. Original text remains intact and the old value survives.
3. Append an emoji while the earlier scalar is partially consumed. The
   existing byte offset survives; only the unconsumed suffix is returned.
4. Advance zero bytes. Queued bytes and offset remain unchanged.
5. Consume the complete input. Storage and offset reset before the next
   command is accepted, preventing replay.
6. Fill the 65536-byte retained storage bound. Each extracted provider prefix
   contains at most 4096 bytes.
7. Append beyond capacity. Refusal does not mutate existing queue state.
   Partially consumed storage still counts until the entire original drains.
8. Reject negative, beyond-submitted and above-4096 advance counts.
9. Reject negative and past-end offsets before enqueueing or advancing;
   extracting from invalid state yields no bytes rather than slicing outside
   the array.
10. Latch an owner-reported deferred write error. Existing input and offset
    survive; subsequent enqueue and advance refuse with that error. Later
    errors preserve the first reason, and an empty reason receives a concrete
    failure message.
11. Change production `PaneRecord` focus, dimensions, output and reply state.
    The partially consumed input remains intact.
12. Change child/PTY metadata or close it. New input ownership starts empty;
    the original immutable pane value remains unchanged. These calls do not
    launch processes or acquire provider handles.

These are pure production queue and record transition checks. Supplying an
accepted byte count or error to a pure helper is not provider execution,
backpressure, fairness, pipe delivery or a native Windows I/O result. Live
provider fixtures must establish those independently. Pending provider output
and deferred completion errors are observable through `smux_input_status`.

After admission, run the spec and docgen once with the exact runtime identity,
record executed case counts and require complete documentation with zero stubs:

```text
<admitted-runtime> test test/01_unit/os/apps/smux/input_queue_spec.spl --native-backend=llvm --assert-ran --keep-artifacts
<admitted-runtime> spipe-docgen test/01_unit/os/apps/smux/input_queue_spec.spl --output doc/06_spec --no-index
```
