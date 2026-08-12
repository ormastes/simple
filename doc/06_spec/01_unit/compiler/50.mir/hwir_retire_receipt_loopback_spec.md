# RISC-V Gen2 verification-only retirement receipt loopback

Executable companion: `test/01_unit/compiler/50.mir/hwir_retire_receipt_loopback_spec.spl`.

## Purpose

This bounded host model tests the reset-coupled receipt transport required by
the future Gen2 scalar commit owner. It has exactly one pending dispatch slot:
an accepted tuple is returned once on the next non-reset cycle, then erased.

It is deliberately **not** a hardware emitter, a scalar execution unit, an
architectural-effect model, or an exact-once retirement certificate. Its public
production diagnostic rejects those uses until a typed architectural producer
and generated RTL evidence exist.

## Evidence steps

1. Construct the typed plan for RV32 C.JAL and RV64 C.ADDIW critical
   configurations.
2. Accept one `(lineage, parcel, canonical instruction, length)` dispatch
   tuple and require the exact tuple on the following cycle only.
3. Assert synchronous reset while a tuple is pending and while another dispatch
   is offered. Require reset to discard both identities and zero every invalid
   receipt field.
4. Offer a competing dispatch during the pending cycle; require backpressure,
   retirement of only the earlier tuple, and a fully zeroed subsequent idle
   observation.
5. Reject malformed CoreConfig, producer-contract, one-entry scope, one-bit
   input, tuple-width, and stale-empty-slot state before any cycle advances.

The test traces REQ-G2-010 and NFR-G2-006/NFR-G2-011. It is elaboration and
host-model evidence only; self-hosted/GHDL qualification of a real producer
remains a separate blocker.
