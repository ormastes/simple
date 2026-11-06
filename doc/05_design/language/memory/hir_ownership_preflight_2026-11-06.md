# Typed HIR ownership preflight

Build a bounded per-function CFG at layer55 and reuse OwnershipFlow (Read, Move,
Revive, Write) and Place overlap semantics already used by MIR NLL. Symbols identify
bindings; field names are interned within one function to stable projection IDs.
Canonical hir_type_requires_move classifies transfers. Calls consume only when
checked parameter-effect metadata binds the exact local or imported function SymbolId.
Unknown retaining contracts or unsupported HIR forms fail closed in strict mode.

Branches emit distinct reachable successors; loops retain condition/backedge,
break, continue and terminal-return edges. Transfer evaluation precedes revival
of the assignment target. Work/depth exhaustion is an error, never an empty PASS.

Driver preflight validates all retained modules before the first interpreter
invocation. Backend direct entry also validates before Environment construction.
This temporarily duplicates bounded checking for driver-executed modules because
mutable HIR has no immutable, versioned checked-facts capability. It does not
reparse source or create target MIR. Measure this cost once an admitted runtime
exists; a future immutable proof capsule may remove duplicate work without a
forgeable serialized checked Boolean.

This first adapter covers moved-use flow, not full loan/drop semantics. Existing
short-effect admission remains mandatory. Unsupported constructs are explicit
errors; no parser-success, source-only assertion, or unavailable runtime implies
product qualification. Tests must pair real source/HIR invalid transfer cases
with mutually-exclusive valid paths and prove a bad dependency prevents entry
side effects. The legacy route is unchanged.

Imported contracts require a live internal provider index. For typed Interpret intent, successful canonical
frozen-surface admission records compact physical path, source content/semantic
identity, bounded canonical complete-function/effect digests, and resolver SymbolTable identity. Before any
execution, the driver checks each provider against that generation once; missing,
changed, ambiguous, or over-budget owners reject. The receipt is never accepted
from serialized metadata. The source identity is the retained admission identity,
not a fresh filesystem read. Re-admission is required after changing source/HIR.
The public direct backend has no provider argument and refuses imported owning
calls without that live context. Local supplied rows are recomputed with canonical
infer_param_effects and compared against exact declarations. The direct entry
first bounds CFG capture, then bounds canonical whole-HIR input to 64 KiB and
16,384 writer work units; inference retains its existing eight-round cap. This
is a bounded-input precondition, not a measured latency guarantee. Internal package callers must obey the trusted
typed-HIR precondition; this is not the final immutable proof/cache capability.

Write validates moved strict ancestors without reading the exact assignment
target; explicit Revive follows successful assignment. Owning non-place short
arguments fail closed except fresh aggregate literals whose contents are moved.
Owning globals/captures fail closed until interprocedural effects exist; scalar
copy globals remain supported. These refusals are incomplete language coverage,
not implementations of the remaining global/derived-view obligations.

Verification status (2026-11-07): reconciliation source review is clean,
conditional on the separately reviewed current codec integration.
Source-to-HIR and subprocess entry controls are authored but NOT_RUN. The core
AST interpreter and cached SMF/JIT paths remain outside this slice. No complete
AC-OWN parity, full borrow/drop safety, or FV obligation is claimed.

The separate codec owner reconciled generated encoder traversal/depth guards
onto the current release declarations; writer byte counters alone did not bound
recursive traversal. Source review is clean; runtime resource admission remains
NOT_RUN. Receipt
encoding is not required for AOT/JIT mode and grants those routes no new claim.

Cycle4 is a targeted repair of review3's classifier-before-bounds finding. The
user AGENTS.md permits at most6 verify/fix cycles and takes precedence over the
earlier stricter3-cycle lane guidance; count3 is retained, not reset. Every strict
module ingress now encodes the complete typed HIR under the canonical guarded
work/depth quota before CFG capture or recursive classifiers, and charges that
work against the module budget. Projected expression type classification also
requires bounded type identity first. Deep Optional/Result/Tuple parameter and
projection rejection specs are authored, NOT_RUN. Targeted review4 closed the
ordering finding by source inspection. All four prior repair cycles remain
counted; at most two further cycles remain under the user cap.
