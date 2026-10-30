# Class static factories missed synthesized generic impl ownership

Status: open — source patch reviewed; actual P3/native qualification pending.

The flat AST bridge deliberately emits class-body methods in a synthesized
inherent impl and leaves ParserClass.methods empty. HIR retains that split.
The existing class-static template collector traversed only HirClass.methods,
while the generic-impl collector explicitly skipped static methods. Consequently
Future<text?>.from_value and Future<text?>.pending retained static method calls
through monomorphization and their unsubstituted T reached MIR. Native focused
logs show both static resolution arms; direct typed constructor controls pass.

The patch collects static methods from exact canonical inherent owner impls as
well as an owner's direct method table. It accepts matching declaration-order
owner/impl binders and canonical positional targets, and excludes trait impls
and method-local generic scopes. Canonicalization includes exact owner and impl
binder SymbolIds; the specialization still binds one argument per owner slot.
Identical candidate symbols deduplicate, while distinct methods conflicting on
the same canonical owner/name remain rejected. It does not change MIR generic
validation, invent missing arguments, or substitute unrelated names globally.

Baseline qualification used the pinned gen13 bootstrap interpreter under the
canonical 3GiB/120s guard. The exact nested Poll<T>/Future<T> fixture executed
two tests: representation characterization passed and factory specialization
failed (zero rewritten factory calls versus two expected). Peak RSS was
1,036,768KiB, raw status1, quiescent1, input hashes unchanged. Retained evidence:
build/verify/static-factory-owner-generics-baseline-20261025-01 in the review
worktree. This is compiler-pass interpreter evidence, not actual native proof.

@openbug: actual P3/native qualification of original factories remains pending.
@workaround: concrete typed Future/Poll constructor call sites are a separately
validated containment; do not claim the underlying generic factory bug fixed
until the original factory source passes genuine native compilation and runtime
checks. No Phase2, runtime, or Rust rebuild was performed for this repair.

Post-patch compiler-pass run: nine examples executed, seven passed, two failed,
zero skipped/dropped. Exact canonical alias substitution in parameter and nested
result signatures, canonical owner isolation, trait/noncanonical target rejection,
and identical/conflicting candidate identity contracts passed. The two full
specialization examples reached an interpreter typed-ABI error at rt_enum_id
(enum argument to dynamic SFFI), so they do not establish successful rewritten
calls or MIR. Peak RSS1,276,880KiB, raw status1, quiescent1, hashes unchanged;
retained under static-factory-owner-generics-postpatch-20261025-01. The original
nested tests remain unchanged and failing; no runtime/SFFI gate was weakened.
A separate scalar-only diagnostic is additional evidence, never a replacement
for the original nested factory qualification.
