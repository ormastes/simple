# StringLit optional-array substitution shape

Issue: https://github.com/ormastes/simple/issues/3049 (bug).
Status: source mitigation candidate; runtime verification pending. No compiler
build or test execution was started in this source-only lane.

The C36 mono-deferred manual replay reports `collection mir type: Tuple` at
`type_subst.spl:599:29`, in the loop over the bound interpolation list. Its
`error-groups.json` is under C06
`build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/mono-deferred/`.
The same code is present in C37 revision
`c9cb8d6ac95ab64c95dc74c46772d2c60002271e`.

`hir_definitions.spl:569` authoritatively declares StringLit interpolations as
`[HirInterpolation]?`. Optional handling is correct and must remain: codec
decoding may construct `Some(list)`, and absent and present-empty lists differ.
The inference failure occurs while traversing the unwrapped enum payload; its
precise compiler cause has not been proved. The candidate records the declared
array type explicitly after `if val` binding and iterates that typed local.
It retains recursive child substitution, all metadata, and absence handling.
The native loop type gate is unchanged.

`stringlit_type_substitution_spec.spl` applies a real T-to-i64 substitution to
nested cast and expression types. Full codec equality against independently
constructed expected HIR checks the child types, literal, format, and spans.
Fresh, explicit Some, and codec-decoded inputs are covered, including nil and
present-empty arrays. Nonempty cases must change bytes, so an identity pass
cannot satisfy the oracle.

The spanless `B5b: match has multiple wildcard arms` in the same replay remains
unattributed. This candidate does not claim that changing the loop fixes it.
The parent manual replay owner must verify the candidate's HIR/MIR behavior and
run the focused regression using the assigned runtime before accepting a pass.

Canonical tracking: `stringlit_optional_array_owner_2026_10_11`, OPEN in `doc/08_tracking/bug/bug_db.sdn`. Reviewed source `34f9b5b775b0332744aa02b3aa4839cefbbc7825` maps to local integration `caad668d19c0e4a70bfdbca200952f6705b022ee`; neither this mapping nor source review claims release landing or native success.

Removal condition: Repair optional enum array payload owner propagation; restore unannotated traversal only after actual deferred HIR/MIR/object and fresh/Some/codec-decoded nested substitution regressions pass. Keep OPEN until a separately qualified permanent repair and retirement.
