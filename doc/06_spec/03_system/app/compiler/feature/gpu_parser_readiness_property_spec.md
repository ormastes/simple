# GPU Parser Readiness Property Gate

**Status:** RED / preparation only  
**Source:** `test/03_system/app/compiler/feature/gpu_parser_readiness_property_spec.spl`  
**Requirements:** REQ-001, REQ-003, REQ-005, REQ-006, REQ-008  
**Importance:** critical (3), high (2), normal (1) per scenario metadata

## Purpose

This manual records the pre-GPU parser property gate. It distinguishes the
CPU-reference evidence that exists today from GPU-readiness evidence that is
not yet owned. It does not imply that a GPU parser is implemented.

## Scenarios

1. **GPU-PREP-V001 — Grammar manifest completeness and digest**
   - Validates the flat lexical manifest shape.
   - Rejects malformed table shape.
   - `MissingEvidence`: per-dialect generated manifest registry and digest:
     the Simple digest binds compiler/interpreter, native+Wasm Tree-sitter
     projection, and `.shs`; SDN binds `SdnDialect`; and
     `src/os/apps/shell/**` binds `SoshDialect`.
   - `.shs` is full Simple plus `std.shell` imports; it is not `SoshDialect`.

2. **GPU-PREP-V002 — Progress, bounded lookahead, and lexical composition**
   - Exercises finite scalar progress and transition bounds.
   - `MissingEvidence`: no-epsilon-cycle/model-checker and chunk composition.

3. **GPU-PREP-V003 — Stack/action/arena and capacity bounds**
   - Rejects source-byte capacity overflow before emission.
   - Checks token count against the output receipt under sufficient capacity.
   - `MissingEvidence`: exact count/scan/emit and one-over receipts.

4. **GPU-PREP-V004 — Region partition soundness**
   - Confirms clean scalar fingerprint repeatability.
   - Observes the current partition seam's explicit unsupported result.
   - `MissingEvidence`: ordered partition equivalence and region parser.

5. **GPU-PREP-V005 — Fallback, cancellation, generation, and recovery**
   - Confirms accelerated requests demote to the CPU backend with parity hash.
   - Exercises malformed-byte input through the scalar path.
   - `MissingEvidence`: cancellation/generation admission and UTF-8 recovery.

6. **GPU-PREP-V006 — Clean versus incremental equivalence**
   - Observes the explicit unsupported incremental-plan result.
   - `MissingEvidence`: stabilization, reuse, invalidation, and clean-reparse
     equality.

7. **GPU-PREP-V007 — Generated-consumer equivalence**
   - Establishes a non-empty scalar source fingerprint.
   - `MissingEvidence`: public API and diagnostic parity within each dialect's
     generated consumer set.

## Outcome

The source was executed once in interpreter mode and produced twelve explicit
`MissingEvidence` failures. This is the intended RED result until the named
owners and receipts are implemented. No grammar change, GPU kernel, or GPU
execution claim is included.
