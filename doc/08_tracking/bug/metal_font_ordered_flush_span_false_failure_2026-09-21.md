# Metal ordered font flushes falsely reject an otherwise complete frame

Status: fix-implemented-verification-pending
Severity: P2
Platform: aarch64-apple-darwin
Source baseline: `20245f731db` (`origin/main`)

`MetalBackend.submit_batch()` required exactly one command buffer, commit and
wait for the entire frame. Seven primitive/readback boundaries already flush
pending text to preserve rendering order; the pending glyph cap can also
flush. A text/primitive/text frame therefore legitimately completes two
submissions and was rejected by the final one-submission predicate.

The change counts successful packed flush spans after the completion wait.
Frame totals must have one command, commit and wait per completed span.
Empty flushes add nothing, `begin_frame()` resets the span counter, and a
latched completion failure rejects the frame. The immediate fallback retains
its previous single-span contract; it does not gain permission for per-batch
fan-out. Existing flush sites and GPU dispatch work are unchanged.

Regression artifacts:

- `test/fixtures/metal_font_ordered_spans/main.spl`: two-span transition,
  incomplete commit/wait, empty span, excess submission and original
  single-span cases against the production pure contract.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_free_contract_spec.spl`:
  final-submit wiring, empty flush, frame reset and completion-failure latch.

## Verification boundary

No Simple runtime test pass is claimed. The admitted Phase 2 binary cannot run
`test` directly, so the two-module fixture was submitted to `native-build`
with `--threads 8`, the admitted runtime authority, and an isolated cache.
The first invocation failed admission with `compile-event-journal-missing`.
With the required `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, a bounded monitor stopped
the compiler at **951,296 KiB RSS after 10.66 seconds**, before compiler output
or an executable. This is the separately owned cold-inventory memory blocker.
No further native retry was attempted in this lane.

Compiler SHA-256:
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`.
Local logs and command receipts:
`build/native_probe/metal_ordered_spans/compile-cold.log` and
`build/native_probe/metal_ordered_spans/compile-cold-receipt.json`.

Static acceptance checks cover successful-wait-only span increments, resets,
the seven unchanged ordering flush boundaries, no added submission calls,
module exports, and negative regression assertions. Native predicate execution,
the backend SSpec and real Metal rendering remain pending. TODO 18 stays open.
