# C7 closed MIR DCE observation

Requirement `REQ-C7-DCE-ACTUAL` implements the source-backed extraction and
optimizer integration slice selected under C7 in
`doc/03_plan/generic_formal_verification_hardening_plan.md:63`.
Status: authored source and specs; **runtime, Lean and formal qualification UNRUN**.

## Accepted domain

Both `params_known` and `declared_params_known` must be true, both parameter
arrays empty, no Arg locals, no variadic signature, exact i64 return. The
function has one entry block ending in Ret(Copy local); all declarations are
unique nonnegative, non-ghost i64 locals. Destinations are unique SSA
assignments, and every read must have an earlier definition. The extractor
admits Const(Int,i64), Copy, and ordinary Add over two Copy operands; all
other effects, instructions, types and graphs are explicitly NotCovered.

Exact values propagate from constants through copies and additions. Before
computing lhs+rhs, positive rhs requires lhs <= MAX-rhs; negative rhs requires
lhs >= MIN-rhs. Both thresholds are representable in their respective sign
branches, even when rhs is MIN. No overflowing sum is evaluated. Thus this
closed domain avoids the mismatch between the wrapping BitVec64 model and
LLVM i64 `add nsw`; unknown or overflowing arithmetic is not certified.

## Actual pass integration and snapshots

`dce_mir_extract_v1` copies only scalar instruction fields into a fresh model
array before the optimizer runs. Its normalized artifact hash includes
function symbol/name/entry, admitted local declaration rows, actual return
local, and the full projected instruction sequence. Validation recomputes the
same canonical hash, including the explicit source return anchor, before
reading the target. A nonzero model result register, negative source anchor,
invalid model diagnostic, empty identity or mismatched stored hash rejects
with the snapshot-integrity diagnostic. Public snapshot records remain
mutable: this detects stale/inconsistent evidence, not authenticated or
unforgeable evidence. It is a normalized MIR
semantic snapshot hash, not a binary/source-file hash or producer identity.
The source's return ID is swapped bijectively with register zero, which is the
Lean theorem's fixed observation register. The target must retain that exact
actual return ID and uses the same swap; it is never normalized independently.

`DeadCodeElimination.run_closed_with_validation` uses the real pass class,
builds a fresh block/instruction array and independent admitted local/signature
arrays, then extracts and validates the actual candidate. Unsupported source
returns NotCovered; invalid or changed target returns Rejected. Only Covered
publishes the candidate and increments statistics. No caller MIR array is
mutated while constructing or rejecting a candidate. The explicit
`run_on_function(func, true)` mode enters this path. Existing default behavior,
inactive registry status, and the exported no-op wrapper remain unchanged.
This is not an enabled ordinary compiler pipeline claim.

## Exact one-pass relation and complexity

The reverse needed set starts with the result register. For each source
instruction, record needed[destination] BEFORE clearing destination and adding
ALL source reads, including reads of instructions removed in this pass. This
is exactly `reads_i(r) OR (r != dest_i AND Live_(i+1)(r))`. Reverse flags append;
forward matching uses n-1-index. No array prepend, suffix rescan, path
enumeration or key snapshot is used. Dictionary membership/value lookups,
not dictionary length, drive liveness and SSA. Expected time and memory are
O(instructions + locals). Performance is a source complexity argument, not a
measurement. The existing abstract optimize/dead-query APIs remain unchanged,
including their legacy invalid-input behavior; only the validator is linear.

This model removes a dead chain's final consumer in one pass; it does not
remove the whole chain transitively. Each subsequent pass is validated against
its own before snapshot. Abstract repeated destinations, undefined/negative
read registers and all existing diagnostic behavior remain compatible; the
actual MIR adapter imposes its stricter domain separately.

## Trust and remaining ledger

Covered means only that this structural relation accepted actual projected
MIR. No CompilerCertificate, independently_checked flag, kernel result or
formal PASS is produced. C7 still requires qualified compiler/runtime artifact
binding, independent checker/audit provenance, actual Result ABI observations
for both outcomes and corruption, and unsupported/general MIR routes. C1–C6
are not discharged by this slice. All executable verification is UNRUN.

Tests: `test/01_unit/compiler/mir/dce_mir_translation_validation_spec.spl` and
`dce_translation_validation_linear_spec.spl` in the same directory. Independent
source review is pending; review/fix cap is three cycles. No compiler retry,
policy, trust resolver, backend semantics, or ordinary dispatch is changed.

## Revision 2 review corrections

Cycle-1 R1 adds canonical consistency checks for every public semantic snapshot
field before target validation. Actual captured snapshots are mutated in the
spec, including a changed program and matching candidate with the old hash.
Cycle-1 R2 retains builder-returned LocalIds in a fixture record; every local
mutation and mapped-record oracle uses those IDs. Both normal reserved-return
allocation and bootstrap allocation are handled without changing environment.
No runtime mode was executed; these are source/API corrections only.
