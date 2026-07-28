# SimpleOS backend render receipt target-operation completion

- Status: open
- Priority: P0
- Affects: REQ-016, REQ-017, REQ-018, REQ-020, REQ-021

## Finding

`BackendRenderReceiptHeader`, `BackendRenderReceiptEvent`, and
`BackendRenderReceiptTrailer` have fail-closed validators, a fixed-width
allocation-free UART codec, and a bounded host parser. The production x86,
ARM64, and RV64 display entries now emit a base BRR1 receipt after their real
present/visual-commit paths, and x86 also implements the correlated hold,
capture, and ACK control flow. The former “no producer/parser” finding is
therefore resolved.

This bug remains open for **local blocker B**: the target-owned no-allocation
per-operation SIMD producers are absent. The implemented shared adapter can
carry fill/copy/alpha/scroll/PRESENT hashes and telemetry, but current target
boot glue does not provide complete native-vector operation evidence across
x86_64, AArch64, and RV64. Host qualification cannot infer those events from a
base frame receipt.

The receipt now carries all four SHA-256 words. Target evidence separately
tracks retained PPM artifact SHA-256 and decoded raw-pixel SHA-256.

## Required fix

1. Implement the x86_64, AArch64, and RV64 no-allocation per-operation SIMD
   owners without duplicating the shared adapter or renderer.
2. Emit real fill/copy/alpha/scroll and PRESENT hashes, executed-path counters,
   fallback counters, and scalar-parity telemetry into the ordered BRR1 events.
3. Join the parsed events to the existing build/boot/frame identity and exact
   independently decoded QMP framebuffer digest.
4. Keep corrupt, reordered, duplicated, truncated, incomplete, zero-hash,
   mismatched, scalar-only, and missing-operation records red.
5. Replace whole-frame temporary byte-array hashing with a bounded streaming
   SHA path before framebuffer sizes exceed the current safe allocation bound.

## Acceptance

- Focused wire/adapter/target-owner specs pass without placeholders, then
  `simpleos_render_evidence_protocol_spec.spl` passes 4/4 on a fresh admitted
  Stage-4 binary and retains the serial log plus QMP PPM.
- Aggregate row `simpleos_guest` promotes only after all required guest targets
  retain correlated receipts with zero pixel mismatches, including strict x86
  VirtIO evidence.
- Aggregate row `simpleos_simd` promotes only after every target retains
  positive native vector chunks and zero required fallbacks for fill, copy,
  alpha, and scroll across ten fresh boots.
- Reordered/truncated receipts and capture identity disagreement remain red.

## Current verification state

- Allocation-free guest bytes, bounded host round-trip, build/boot identity,
  base x86/ARM64/RV64 emitters, and the shared per-operation adapter are
  implemented. They do not complete the missing target SIMD owners.
- The third codec cycle exposed an unparenthesized multi-line condition. Source
  is corrected, but the hard three-cycle cap forbids another run this session.
- Resume exactly:
  `SIMPLE_LIB=src <fresh-stage4> test test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl --mode=interpreter --clean`.
- TODO317 owns only the later admitted native/live-host evidence. This local
  producer work must land before that evidence can promote a row.
