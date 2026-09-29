# SimpleOS backend render receipt producer/parser missing
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Status: source repair complete in `codex/simpleos-render-receipt`; target
verification remains open (2026-09-22).

The guest producer is now `os.compositor.backend_render_receipt_producer`.
The x86 production entry calls it only after the presentation owner admits the
first frame, using the exact scanout object, a host-generated launch nonce, and
the admitted kernel SHA-256 read from `/SYS/KERNEL.ADM`. Pixels are streamed
from the committed framebuffer through 256 bytes of scratch instead of copying
the 4K scanout into bump-allocated pixel and canonical-byte arrays. Fixed-width
receipt records are written directly to the architecture UART byte owner.

2026-09-23 source repair: presentation receipts now retain the full scalar
scanout identity admitted by their owner. Both producer paths reject a receipt
reused with another scanout. The production framebuffer reader also compares
the presented address with `FramebufferDriver.front_addr` before any MMIO read,
validates bounded geometry, and rejects duplicate/prefixed admission digests.
The address remains outside the presentation owner and the wire protocol.

The canonical fullscreen wrapper now generates eight random bytes for every
launch and stages `capture_boot_nonce` in a separate run admission record,
including cached-kernel launches. Guest parsing requires exactly one nonzero
16-digit nonce and a valid kernel admission; it has no guest-clock fallback.
Before host capture, the wrapper requires exactly one receipt header matching
that nonce and records identity status in the report. External disk images do
not acquire a fabricated identity claim. The regression feeds a prior-boot ACK
to a new boot with the same frame/scanout IDs; it must reject despite equal
guest elapsed time. The new host header comparison uses string comparison to
avoid loss of precision for decimal-only hexadecimal values.

Lightweight host validation passed: the exact AWK program extracted from the
runtime wrapper accepts one matching header and rejects missing/duplicate
headers and nonces `9007199254740992` versus `9007199254740993` (which would
alias under floating-point numeric comparison). Shell syntax checks passed for
the build/runtime/report fragments. The 14-example Simple producer spec,
including prior-boot ACK rejection, remains deferred to the admitted runtime.

This draft is scoped to the x86 receipt producer and per-launch identity
boundary. W/A/K transport and frozen-pixel capture are NOT implemented or
verified here; the report explicitly records `render_capture_ack_status` as
`not-implemented`. This bug stays OPEN, and receipt identity alone cannot admit
the aggregate correlated-render evidence gate.

Memory/performance boundary: SHA state/schedule/block arrays and the 256-byte
scratch buffer are fixed size, with at most one bounded tail copy. Hash work is
linear in pixels. Production creates this state once before the desktop frame
loop, so bump-allocator use does not grow with frame count. This is source
analysis, not measured target timing or allocator evidence; the public producer
is not advertised as allocation-free when called repeatedly.

TODO when an admitted x86 Linux runtime is ready: execute
`test/01_unit/os/compositor/backend_render_receipt_producer_spec.spl`,
`test/01_unit/os/compositor/baremetal_wm_present_owner_spec.spl`, and
`test/01_unit/os/compositor/baremetal_wm_present_entry_wiring_spec.spl`.
New behavioral cases cover wrong scanout identity, equal geometry at a wrong
address (reject before unmapped MMIO), malformed admission, and SHA digest parity
across a full scratch chunk plus tail. No Rust seed substitutes for these tests.
Measure first-frame qualification time and bump-heap usage at 1080p/4K after
Linux bootstrap, and confirm no receipt work/allocation enters the frame loop.

Deferred target TODO: stage the admission record in the canonical QEMU image,
exercise the `W/A/K` hold/capture/ACK exchange, retain serial plus QMP pixels,
and repeat the correlated gate on x86_64, AArch64, and RV64 and supported boards.
Until those runs pass, this change claims source correctness only—not live
rendering, QEMU verification, or board verification.

- Status: open
- Priority: P0
- Affects: REQ-016, REQ-017, REQ-018, REQ-020, REQ-021

## Finding

`BackendRenderReceiptHeader`, `BackendRenderReceiptEvent`, and
`BackendRenderReceiptTrailer` now have fail-closed validators, a fixed-width
allocation-free UART codec, and a bounded host parser. The x86 production entry
now emits a one-shot present receipt; AArch64/RV64 integration, ordered operation
events, and the guest hold/host capture/ACK integration remain incomplete. QMP
pixels are therefore not yet proven to match the emitted receipt.

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
- Aggregate row `simpleos_guest` promotes only after all required guest targets
  retain correlated receipts with zero pixel mismatches, including strict x86
  VirtIO evidence.
- Aggregate row `simpleos_simd` promotes only after every target retains
  positive native vector chunks and zero required fallbacks for fill, copy,
  alpha, and scroll across ten fresh boots.
- Reordered/truncated receipts and capture identity disagreement remain red.

## Current verification state

- Allocation-free guest bytes and bounded host round-trip passed 5/5 before the
  full target-evidence join was added.
- The third codec cycle exposed an unparenthesized multi-line condition. Source
  is corrected, but the hard three-cycle cap forbids another run this session.
- Resume exactly:
  `SIMPLE_LIB=src <fresh-stage4> test test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl --mode=interpreter --clean`.

