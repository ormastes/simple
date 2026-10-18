# Generic enum template-only native scheduling

Status: source candidate; all new executable tests UNRUN. No compiler or native
build was launched for this candidate. Existing authority/Future receipts remain
unchanged. This requires a genuine compiler cohort containing the driver change.

The executing f048 producer's `_compile_selected_module` rejects a MIR module
with zero functions and statics before backend emission. Poll owns an enum and
generic instance methods, which successful HIR lowering retains as templates;
MIR deliberately skips those templates. The existing parser proof rejected all
impls, so this legitimate zero-runtime-definition module reached codegen.

The candidate widens the existing source-bound parser proof only for inherent
impls of local generic enums. The canonical parser represents a positional
generic impl target as an argless Named type and records its parameters on the
impl; concrete, nested and reordered targets carry an opaque applied argument.
Require matching nonzero parameter arity, distinct unbounded parameters, and
ordinary instance methods. Reject trait impls, associated types, constraints,
static/foreign/async/kernel/attributed/method-generic cases and nonlocal owners.
Existing module restrictions on concrete free functions and data remain.

Classification does not bypass HIR lowering: full method bodies still lower and
are retained in canonical HIR payloads before proof capture. Existing
source/path/module identity checks and final MIR functions/statics/constants
emptiness remain mandatory. A concrete specialization prevents omission and
requires its normal real object. The existing scheduler records OBJECTLESS
before capsule construction, object-cache publication and link-input collection;
there is no fabricated object path, symbol, digest, or initialization call.

The source-branch candidate removed the fallback that compiles `simple_empty_module_*` C globals;
see the port note below. Unproven empty units should remain errors; empty MIR alone proves nothing.
The unrelated opt-in bootstrap empty-object route is not enabled or used here.

Regression scope: real parser representation, retained HIR method bodies and
template flags, real empty MIR, renamed parameters, rejected concrete/nested/
permuted/nonlocal/static/concrete-function/data cases, trait defaults, changed
source/path, absent proof and actual nonempty lowered MIR. No native PASS,
whole-compiler qualification, link qualification or deployment is claimed.

Port note (release_phase3 sync 2026-10-19): the port onto release_phase3 keeps
upstream's `simple_empty_module_*` fallback in `_compile_selected_module`
(added upstream by 1670c0f64ea for entry-closure re-export facades). Only the
parser-proof widening for generic enum templates is ported. Removing that
fallback is an owner decision and is not part of this port.

## Native cycle 1 and prerequisite ownership repair

The frozen a9b51ff085996045706c9b91ae95f3c1db6103ad run selected 992 sources,
completed 12 parse workers, then stopped during HIR with three failed modules:
builtin_blocks_shell, builtin_blocks_data and builtin_blocks_math. HIR reported
three completed and three failed workers, three failed modules and no unfinished
work. The harness never reached MIR or execution (compile1/runUNRUN). Guard
8805f8d5eb783efa9a472d059a787d79e7c38bf0d86f66a194ebe5e2592ecb82 is complete
and quiescent, peak RSS 11,941,740 KiB. This is not a failed Poll assertion.

The changed-source candidate moves the existing three production proof functions
from heavyweight driver_types into driver_native_mir_objectless_proof. Their
bodies, signatures, source identity format and final-MIR guards are unchanged;
driver_types re-exports the public API. The parser-only proof owner remains free
of MIR imports. Both fixtures now import the actual small production owner.
This removes the direct driver_types dependency without copying test logic or
excluding block files from a source selector. A future canonical dependency walk
must establish the actual reduced closure; no module count is asserted here.
The owner refactor and its executable cases remain UNRUN.

## Cycle 2 evidence and final cycle 3 candidate (2026-10-18)

The frozen 542775adc01b0cc139cc1a19a61c66c707e57d1d source selected 338 files,
passed all 12 parse workers and all 419 HIR modules. Monomorphization then
reported 24 generic functions, 532 call sites, 153 specializations and three
unresolved calls. E-MONO-041 identifies the three `_sffi_tuple_get` calls in
`module_callable_types`; E-MONO-033 stopped compilation before MIR. The native
classification assertions remain UNRUN. Guard
6c761727691a35111fdb698b315e388c30dd1ae74ae7892ae5f11194a7a7c489 is complete,
exit1 and quiescent, with peak RSS 9,446,644 KiB. This is neither an objectless
classification failure nor a native PASS.

The final candidate removes the unused local always-inline wrapper and calls
its existing `rt_tuple_get<T>` foreign declaration directly at those three
sites. Each call has its own `unsafe(capabilities: [ffi])` expression. The
concrete arguments remain `Expr`, `Block` and `Block?`, with unchanged tuple
indices, borrowed payload, optional return semantics and call count. No new
extern, runtime provider, type erasure, owner-identity exception or MIR skip is
introduced. The generic nominal specialization bug remains open; this is a
source workaround at an existing foreign boundary.

The actual native harness adds three return-scanner checks using parsed source:
present else, absent else, and incompatible branch return types. They invoke
the production scanner and check the resolved scalar type, return presence,
ambiguity and error count. All existing cold/retained proof, retained template
body and nonempty specialization assertions remain. Source and execution
qualification for this candidate are pending review; no cycle 3 execution has
occurred, and there is no authorized fourth Poll cycle. Bug tags and database
reconciliation are owned by other sessions.

The source-only SFFI unsafe audit stopped at its dependency's aggregate migration
ceiling: 3,553 entries against 3,546 allowed; source signature variants were 278
against 399 allowed. This candidate changes no extern declaration or signature.
The aggregate audit is FAIL, not admission evidence; no ceiling was raised.

Port note (release_phase3 sync 2026-10-19): the cycle-2 owner refactor into
`driver_native_mir_objectless_proof` described above was not part of the ported
commits; on release_phase3 the proof functions stay in `driver_types`, and the
fixture imports them from there.
