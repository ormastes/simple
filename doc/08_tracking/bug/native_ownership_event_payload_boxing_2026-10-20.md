# Native enum payload loses its type at array insertion

Observed with admitted r17 Stage 2 producer, SHA-256
`29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`.
This is a route-specific executable defect; current-source or other-backend
parity has not been established. This note records evidence, not a Bug DB
migration or a resolved compiler defect.

The initial `nogc_ownership_flow_probe.spl` closure compiled four modules and
linked successfully (83.06 seconds, max RSS 4,013,640 KiB). Execution crashed
in `ownership_contains`. GDB showed its Place candidate was a heap pointer
multiplied by eight. Disassembly of `ownership_event_transfer` shows
`rt_value_int_wide` immediately before `rt_array_push` in the Move arm:

`case OwnershipEvent.Move(place): ... state.push(place)`

The declared payload is `Place`, not an integer. The wrong integer boxing
corrupts the stored place; a later join reads it as a struct pointer and
segfaults. Evidence is retained under `build/nogc-hardening/ownership-flow-*`
(build, run, GDB caller/registers and transfer disassembly logs).

An explicit local binding `val place: Place = operand` before generic array
insertion did not repair the executable: build 2 succeeded (75.16 seconds,
max RSS 4,056,940 KiB), then reproduced the same segfault and integer boxing.
The source now additionally uses a typed-parameter insertion helper, matching
the existing BorrowGraph recorder boundary. The native probe must execute
after rebuilding to establish whether this mitigation works.
Do not call the producer defect fixed solely
because the annotated form passes. A permanent compiler fix must preserve
declared enum payload types through pattern binding and generic array calls,
with an unannotated cross-module payload regression on an admitted producer.

Build 3's typed-parameter helper did avoid the observed corruption: the
native diagnostic exited 0 and completed its branch/backedge/revival and
malformed-fact corpus. Build: 74.36 seconds, max RSS 4,099,376 KiB. Verified
solver-source SHA-256:
`c04c7a43ae184c865d4d96257f14f770782898c9d2c2cac821c9200976f04ebe`.
This establishes that particular mitigation, not a compiler correction.
Explicit array snapshot copies were added after this build snapshot and
remain unexecuted. `ownership-flow-build-3.log` and
`ownership-flow-run-3.log` retain the executable evidence.

After explicit user authorization, the final solver including array snapshot
copies and the NLL recorder integration both compiled and exited 0 on the
same producer. Final solver SHA-256:
`8eacce51b3074c95058efc9d2092313eba503c33d43b54a3de38f2a859b14d69`.
Logs: `ownership-flow-final-build.log`, `ownership-flow-final-run.log`,
`nll-flow-build.log`, `nll-flow-run.log`. This supersedes the pending-execution
note for the snapshot-copy edits; the producer's unannotated payload-boxing
defect remains unresolved.

### 2026-10-21: optional binding loses nominal enum-constructor evidence

Frozen redeploy revision v3's `manual-module-lowering-build-3.log` ended with
13 failed modules after 1,032 seconds. In `builtin_method_extras.spl`, the
three final diagnostics name `compiler.hir.hir_types.HirTypeKind.Array`
(two sites) and `.Named` (one site). These uniquely identify the file's two
Array constructors and sole Named constructor: the optional bindings
`known_elem_hir`, `value_hir`, and `rebound`. Their payload traces report
`remembered=none source=none mir=present` at line 0, despite the producers'
contracts returning optional HirType and SymbolId records respectively.
The line-zero trace lacks constructor/function provenance; numeric module-local
`named#99`/`named#2` alone was insufficient to identify the source sites.

The completion worktree now rebinds both array elements as concrete HirType,
and the exact-owner lookup result as SymbolId, before constructing those enum
payloads. The Named generic arguments also retain an explicit `[HirType]`
binding. Existing exact-owner checks, element semantics, and enum validation
remain intact. This is a bootstrap-compatible source mitigation; no rebuild
has qualified it, and no producer correctness or feature PASS is claimed.
The running/frozen producer snapshot and its cache were not edited.


### SSA Ret owner attribution: unverified direct-owner mitigation

The cold, single-threaded, HIR-cache-disabled control reports a Ret pattern
attributed to HirExprKind while the SSA source subject is explicitly typed
MirTerminator. SSA analysis and rewriting previously imported MirTerminator
through the mir_instructions compatibility facade. The completion sources now
import it directly from its declaring mir_instruction_support module and
qualify only their Ret patterns as MirTerminator.Ret. This preserves the
terminator arms, operand validity checks, and the concrete carrier guard leaf.
This is an unverified bootstrap compatibility measure, not evidence that the
facade caused the owner mismatch or that the producer defect is repaired.
No frozen producer source or diagnostic cache was changed for this edit.

### Proven source error behind the remaining HirExprKind Ret diagnostic

The manual module build 6 closure includes `compiler.mir.synthetic_driver_registration`.
Its `expr_find_register_static_driver_call(expr: HirExpr, ...)` matched
`expr.kind` with `Ret(value)`, although the declared HirExprKind variant is
`Return(value: HirExpr?)`. This is a concrete source typo, independent of the
earlier speculative SSA owner-transport explanation. The completion source now
uses `HirExprKind.Return(value)`; the existing Some/nil recursion is unchanged.
HirExprKind was already imported directly from hir_definitions. No rebuild has
qualified the correction. The earlier SSA direct-owner mitigation remains
unverified and must not be credited with repairing this diagnostic.
