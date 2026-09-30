# Native relative import emits duplicate physical and logical alias objects

Status: reproduced in retained producer 908; no source fix in this change.

A tiny entry `src/app/hir_owner_probe/main.spl` imports its sibling module with
`use hir_owner_name_reference.{reference_owner}`. Native object compilation
produces both `object.hir_owner_name_reference.o` and
`object.app.hir_owner_probe.hir_owner_name_reference.o`, each defining
`app.hir_owner_probe.hir_owner_name_reference.reference_owner`. A strict link
reports a multiple definition.

`nm -g` defined/undefined symbol lists and `objdump -dr` instruction/relocation
streams were exactly equal. For the isolated normalization diagnostic only,
the final link input omitted the redundant logical alias object. Both cached
objects were preserved, and no `--allow-multiple-definition` option was used.
The resulting fixture is not evidence that producer module-alias linking works.

Evidence:
`/mnt/simple-bootstrap-6b2/hir-owner-perf-fix-20260930/link-resume/alias-object-equivalence.json`,
`result.json` (initial duplicate failure), and `final-result.json` (explicit
diagnostic link command, input manifest and first test result).

A separate producer correction must canonicalize equivalent module object
inputs without dropping distinct definitions. Regression coverage should import
the same sibling by relative and canonical names and require an ordinary strict
link to succeed without duplicate definitions or multiple-definition suppression.
