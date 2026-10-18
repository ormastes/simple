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
