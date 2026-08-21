# Stage-3 streaming surface parse nondeterministic SEGV (2026-08-21)

## Status

Concrete owner-lifecycle defects fixed locally; causal confirmation and
bootstrap re-verification pending. The admitted Stage-2 compiler crashed while
building Stage 3 before HIR lowering. No seed fallback is accepted.

## Evidence

Two cache-preserving full-closure attempts with the same compiler and source
identity ended at different Phase-2 parse boundaries:

- `src/compiler/mir/hwir/aspects.spl`, after 40 surfaces were released;
- `src/std/nogc_sync_mut/io_runtime.spl`, after 5 surfaces were released.

Both terminated with signal 11 and no compiler diagnostic. The isolated HWIR
entry-closure mini-build compiled 28 modules, linked a 62 KB executable, and the
executable returned zero. Therefore `hwir/aspects.spl` is not a deterministic
source parser failure; the varying boundary points to full-closure transient
owner/runtime corruption.

## Ownership audit

The first hypothesis—lexer replacement arrays being reclaimed at scope end—was
excluded: both cleanup paths pause the scope before replacement, and paused
allocations are persistent. End-before-replace is now pinned as the canonical
defensive order, but it is not claimed as the crash fix.

Two actual lifetime violations were found in active parser state:

- `par_errors`, `par_warnings`, and `par_struct_names` kept process-lived array
  headers while `push()` could replace their backing inside the transient
  scope. The next file used `clear()` on potentially reclaimed backing.
- `file_generic_constraints` and `file_generic_constraint_modes` accumulated
  file-local token strings and arrays across scopes without reset or promotion.

Parser initialization now replaces the three scratch owners before reading
them and resets both generic-constraint dictionaries for every file. A source
contract pins these owner-local resets. These fixes satisfy the lifecycle
invariant, but only a fresh full-closure run can establish that they explain all
observed SEGVs.

## Reproducer

Use the admitted Stage-2 executable and preserved Stage-3 native cache recorded
by `build/bootstrap/stage3/*/stage3-command.transcript`. Set
`SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_STAGE3_STREAMING_SURFACES=1`.

## Next investigation

In a fresh bounded session, rebuild the admitted Stage 2 and rerun the
receipt-bound Stage 3 once. Preserve the cache and verify that all Phase-2
surface releases complete before evaluating HIR or Stage-4 convergence. Do not
patch the file named by a final progress marker.
