# MIR trait lookup scope retention

Status: source fix proposed; native regression and memory improvement unverified.
Bug ID: `mir_trait_lookup_scope_retention_2026-10-18`.
Bug DB reconciliation is pending: the qualified normal DB tool is unavailable.

Release base: `2414f2755c76f1d22ffdceb546657db442d7e68d`.
Live-build source inspected: `74113e7661e87b66cd9068399b3136274234debf`.
The live build, immutable producer and caches were not modified.
That revision is the target input, not the compiler executable's baked source.
The parent review also confirmed both lookup fields and their owner promotions
in the executing producer's `ee3` source tree at
`C:/dev/simple-phase2-value-diagnostic-producer-20261017`.

`MirLowering.lower_module` replaces `native_trait_layouts` and
`native_trait_implementations` before registering the current consumer and its
providers. Both arrays are lookup scratch for registration, conversion, calls
and dispatch. `promote_transient_owner` nevertheless promotes both at every
successful scoped module boundary. Runtime promotion clears the transient owner
scope; replacing the roots next module does not reclaim those promoted versions.
This establishes unnecessary promotion, not its contribution to measured RSS.

The patch detaches exactly these two roots after `lower_module` returns and
before pause/promotion. It does not explicitly free any child. The completed
module, builder, native trait thunks, provider declarations, diagnostics and
global registries retain their existing promotion paths. Shared children that
are genuinely reachable from completed MIR or another retained root remain live.
The synchronous lifted-lambda lowerer borrows the lookup arrays, returns before
this boundary, and exports generated thunks rather than the lookup arrays.

Scope-begin refusal still takes the existing unscoped fallback. A pause or later
ownership failure follows the existing abort path and returns no module. This
change does not address those paths or the whole-MIR-to-object phase barrier.

The focused specification is
`test/01_unit/compiler/50.mir/trait_scratch_scope_retirement_spec.spl`.
It parses real trait/class/implementation source, checks emitted indirect calls,
vtables and thunk signatures, lowers a second module with the shared provider,
then re-reads the first module and input HIR. Diagnostic JSON is used only as an
instruction-graph comparison, never as a lossless archive.

Native execution is UNRUN: no qualified pure-Simple full CLI is available, and
the active build's memory reservation excludes another compiler run. Therefore
this report makes no native qualification, all-object completion, memory-budget
or RSS-reduction claim. A qualified native regression and bounded before/after
memory measurement remain required before claiming the retention reduction.

The MIR source-boundary guard also remains FAIL, not PASS. Both the patched
worktree and a snapshot of the untouched release base report exactly the same
17-invariant result (exit 1): `driver-entry-closure-loop-not-scoped`,
`driver-fallback-loop-not-scoped`, `owner-field-inventory-drift`, and
`unpaired-error-returns=8`. The guard SHA-256 is
`8c041e5d305f655e24a524dabb970172826ac1a35c7f93cb2c364c466052f3e4`;
the release-base tree is `379014f6fff10fef11b52dc326aa9a89505f8272`.
No unrelated guard repair is included.
