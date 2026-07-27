# SimpleOS backend render receipt producer/parser missing

- Status: open
- Priority: P0
- Affects: REQ-016, REQ-017, REQ-018, REQ-020, REQ-021

## Finding

`BackendRenderReceiptHeader`, `BackendRenderReceiptEvent`, and
`BackendRenderReceiptTrailer` now have fail-closed validators, a fixed-width
allocation-free UART codec, and a bounded host parser. No production SimpleOS
guest entry emits the ordered records yet. Current guest entries expose static
frame markers, so QMP pixels still cannot be bound to firmware, boot, frame,
surface, or operation identities.

The receipt now carries all four SHA-256 words. Target evidence separately
tracks retained PPM artifact SHA-256 and decoded raw-pixel SHA-256.

## Required fix

1. Emit one header, ordered fill/copy/alpha/scroll or backend-operation events,
   and one trailer from each qualifying x86_64, AArch64, and RV64 guest entry.
2. Inject a real build identity and per-boot identity; do not use constants.
3. Reject corrupt, reordered, duplicated, truncated, incomplete, zero-hash, and
   mismatched boot/frame records.
4. Add guest hold/host capture/guest ACK correlation, then join the parsed
   record to exact QMP framebuffer evidence without using the canned
   `probe_qemu_vm_screendump` scene.

## Acceptance

- `simpleos_render_evidence_protocol_spec.spl` passes 4/4 on a fresh admitted
  Stage-4 binary and retains the serial log plus QMP PPM.
- `simpleos_engine2d_guest_backend_equivalence_spec.spl` passes all required
  guest targets with zero pixel mismatches.
- `simpleos_engine2d_simd_matrix_spec.spl` reports positive native vector chunks
  and zero required fallbacks for every operation and target.
- Reordered/truncated receipts and capture identity disagreement remain red.

## Current verification state

- Allocation-free guest bytes and bounded host round-trip passed 5/5 before the
  full target-evidence join was added.
- The third codec cycle exposed an unparenthesized multi-line condition. Source
  is corrected, but the hard three-cycle cap forbids another run this session.
- Resume exactly:
  `SIMPLE_LIB=src <fresh-stage4> test test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl --mode=interpreter --clean`.
