<!-- codex-design -->
# Simple 2D and web renderer GPU optimization detail design

## State machine

Frame slots transition `free -> recording -> submitted -> device_complete ->
presented -> free`. `capture_pending` is an explicit branch after
`device_complete`; it cannot be entered by normal display. Invalid transitions,
generation mismatch, or reuse before retirement return typed errors.

## Integration

1. Add the surface/token/receipt value contracts beside Engine2D session types.
2. Extend each GPU backend adapter with submit, nonblocking completion poll,
   device present, explicit capture, and deterministic release capabilities.
3. Make the Vulkan implementation use fence/timeline values and retained
   per-slot command/staging resources.
4. Replace browser renderer caches of bare engines with surface owners and
   explicit resize/device-loss/shutdown hooks.
5. Remove pixel fingerprint/readback from the steady GPU route; retain it only
   in the explicit evidence sampler.
6. Translate accepted input generations into DrawIR/resource deltas and damage;
   coalesce only unsubmitted generations.
7. Add counters for allocations/bytes, upload/readback, submit/poll/wait,
   frames-in-flight, damage, fallback, and lifecycle releases.

## Benchmark implementation

- Correct `check-vulkan-2d-c-compare.shs` to use an admitted self-hosted native
  Simple binary and independently select timed readback mode for both sides.
- Use the exact-diff harness once, then collect 31 warm device-present samples
  with readback disabled and one post-timing capture.
- Replace cold Chrome process-plus-PNG versus warm Simple paint with a common
  warm event-to-pixels-complete interval, equal samples, common raw pixel format,
  device identity, RSS, and binary/source hashes.
- Reject the legacy synthetic ratio runner and any mixed-source comparison.
- Admit a ratio only when timed buffer allocations, timed full-frame uploads,
  timed CPU completion waits, and timed framebuffer readbacks are all zero;
  retained bytes are nonzero and released at teardown; completion polls and
  event generations cover every sample; and accumulated damage never exceeds
  the total sampled viewport area. One optional RGBA8 capture must contain
  exactly `width * height * 4` bytes and remain outside the timed interval.

## Error handling

All operations return typed unavailable/failure reasons. Surface generation and
backend identity are checked before mutation. Timeout or device loss invalidates
the affected token and surface; it never retries silently on CPU.

The Chromium oracle accepts structured fixtures at the Simple boundary. The
fixture validator owns the exact Electron and Chrome versions plus broker and
lockfile digests; the serializer emits all identity, viewport, content, event,
primitive, and GPU-receipt fields in one escaped request. Callers must use this
typed route so a hand-written raw JSON request cannot omit provenance pins.

## Rollout order

Chrome ABI prerequisite; receipt/state types; Vulkan surface lifecycle;
device-present/capture split; async ring; web cache integration; event damage;
primitive compaction; fair collectors; final cross-backend verification.

The Chrome prerequisite compiler gate uses
`test/fixtures/native_vhdl_builtin_string_resolution/main.spl` as its smallest
entry closure. The fixture deliberately reaches VHDL vector defaulting
(`starts_with`) and source-map scanning (`len` plus `contains`). Its integration
gate must compile with `SIMPLE_NO_STUB_FALLBACK=1`, reject unresolved/unknown
symbols, execute the standalone candidate, and observe the exact PASS receipt
before another full compiler build or Chrome dylib build is admissible.
