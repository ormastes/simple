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
3. Assert synchronous reset while a tuple is pending, then require no stale
   receipt after reset and only a post-reset tuple to retire.
4. Reject removal of the verification-only safety bit and out-of-range typed
   dispatch fields.

The test traces REQ-G2-010 and NFR-G2-006/NFR-G2-011. It is elaboration and
host-model evidence only; self-hosted/GHDL qualification of a real producer
remains a separate blocker.
