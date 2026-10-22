# Imported generic specialization calls lose their defining module

Date: 2026-10-12. Requirement: REQ-COMPILER-GENERIC-SPECIALIZATION-OWNER.
Provisional bug: mono-imported-specialization-owner-2026-10-12.
Authoritative bug database reconciliation remains pending.

An imported `transient_promote<text>` call compiled to the undefined symbol
`transient_promote$str`, while its real provider object exported
`lib.nogc_sync_mut.sffi.transient.transient_promote$str`. The specialization
body existed. Earlier wording that implied it was never emitted is corrected.

`request_specialization` records the owner in `spec_module` and inserts the
specialized function into that owner. `rewrite_call` used `mono_requalify`,
which retained bare or abbreviated import display names. MIR's NamedVar
lowering consumes the display name directly, so it could not find the emitted
definition. Explicit type arguments fixed a preceding inference failure but
could not fix this independent name mismatch.

The locally applied pure-Simple correction derives foreign call names from canonical
`spec_module` ownership. It preserves bare same-owner names and the actual
specialized function's extern/export/global/entry linkage. Missing, empty, or
uncanonicalizable owners and absent retained linkage metadata produce
E-MONO-034 rather than a guessed bare foreign target. No memoization, symbol
alias, stub, runtime replacement, or new retained cache is involved.

Executable regression: `test/01_unit/compiler/mono/mono_specialization_owner_spec.spl`.
The twelve cases execute the real retained monomorphizer on typed HIR. They
cover imported text and array specialization, full and abbreviated nested
owners, same-owner calls, missing and empty owner records, source-path owner
normalization, and extern/export/global/entry ABI names.

Evidence packet: `build/native_probe/mono-owner-20261012/`.
Cycle 1 parser-based fixtures escaped the frozen source closure; that run is
invalid evidence. Cycle 2 actual-owner baseline was 7 total / 2 passed / 5
failed; candidate was 7/7. Cycle 3 checked five new boundary cases on the
baseline (4 passed / 1 failed), then the complete candidate (12/12). Both
admissible cycles verified pinned source confinement, producer image, unchanged
inputs, and closed Windows Jobs. Three-cycle cap reached; no fourth retry.

Producer SHA256:
`d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.
This is a bootstrap-seed source diagnostic against a frozen dependency set,
not an admitted full CLI or a newly rebuilt pure-Simple native compiler.
The current owner patch and frozen owner adaptation have the same naming
correction; their surrounding compiler versions differ.

Native repaired-producer qualification, the closed identity-tail benchmark,
and CPU/time/RSS performance acceptance remain pending. No 0.1-second build
claim follows from these tests. The independent runtime-source discovery
failure also remains open.

ArchiveRequests exists only in the retained donor version, not this branch's
owner. Its body-free signatures omit linkage attributes. Archive qualification
is UNRUN; preserving linkage metadata is a separate prerequisite before any
later archive-mode adoption. The proposal refuses to guess those missing
facts and must not be presented as an archive-mode fix.

Root reviewed specialization insertion before call rewriting, provider
canonicalization and bare-linkage rules, and the final cleanup proof. Applied
current owner SHA256:
`98721e542dc9d4bc8cebfc83dbed2f338add4dda492d4532f4398184a014a837`.
The final repaired function body matches the tested proposal; import placement
and removal of the now-unreferenced old helper are the only cleanup changes.
Selective local application commit: `f26793b4a88`.
Remote landing remains gated on the user's Phase 3 buildability requirement.

Port note (release_phase3 sync 2026-10-19): upstream had independently replaced
`mono_requalify` with `specialization_callee_name_v1`, which names the callee
from the template owner and its signature's global linkage in both body modes.
The port keeps that structure and applies only the missing piece of this fix:
the owner is canonicalized with `hir_symbol_owner_module` before qualifying.
The `spec_module`-based E-MONO-034 rejections were not ported, because upstream's
rewrite path no longer consults `spec_module`; their two spec cases were removed.
The ported spec has not been re-executed on the upstream base.
