# Generated HIR consumers omit sibling helper imports

The Linux Phase2 build of release `d6b569ace4c3ab7b463eab81ac9b2921f032d936`
compiled1129 modules, then failed to link `unreachable_hir_variant` and
`hir_visit_nothing` from `hir_children.spl`. Retained object symbols contain no
definitions for either name. The imported-global dependency traversal makes
this generated module part of the bootstrap entry closure.

Both helpers belong to `generated/hir_visit.spl`. The children generator emits
calls without importing that sibling. The hash generator likewise calls the
exhaustiveness helper without importing it. Re-exporting all generated modules
from the package facade does not supply imports to direct consumers.

The repair adds explicit helper imports in the two generator templates and
synchronizes their checked-in outputs. Existing helper implementations remain
authoritative: leaf visits have no children; an unknown variant exits with a
diagnostic. No replacement helper or unresolved-symbol fallback is introduced.

`test/fixtures/compiler/hir_generated_helpers_native/main.spl` directly imports
both consumers, checks that a literal has zero children and that structural
hashing is stable and changes with the literal. Native acceptance is exit0 and
exact stdout `hir-generated-helpers: PASS\n`. A new frozen producer build and
native execution remain pending; source review is not runtime acceptance.

Failed build evidence is preserved in Debian at
`/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/release-source-d6b569ace4/build/native_probe/integrated-d6-phase2`.
The watchdog completed/quiesced with exit1, peak1621452KiB, cap2097152KiB.
