# scv parser-verify: artifact hash validated AFTER path construction (FIXED)

Date: 2026-08-27
Status: FIXED
Class: (b) real product bug — missing guard / inconsistent defence between two code paths
Found by: root-causing long-standing RED `test/integration/app/scv_parser_wasm_spec.spl` (7/12)

## Symptom
`scv_parser_wasm_spec.spl` example "rejects unsafe parser artifact hashes before
path construction" failed: it asserts `parser-verify` emits

    ERROR unsafe parser artifact hash: foo tree-sitter-foo

for a lock entry whose artifact hash field is `../bad`, but `parser-verify`
instead emitted `ERROR unsafe parser artifact path: ...`. The `fsck` half of the
same example passed, which is what made the split visible.

## Root cause
Two code paths validate parser lock entries and they disagree.

`src/lib/scv/integrity.spl:173` (the `fsck` path) does it correctly — it checks
the hash field first and bails before the path is built:

    if not scv_object_ref_safe(parts[6], "sha256_"):
        errors.push("unsafe parser artifact hash: ...")
        continue
    val expected_path = "{scv_parsers_dir(root)}/{parts[6]}.wasm"

`src/lib/scv/parser_registry.spl` (the `parser-verify` / locked-parser path) had
no hash check at all, at either of its two entry-validation sites (:91 in
`scv_locked_parser_error`, :229 in the lock-verification loop). It went straight
to `scv_parser_artifact_expected_path(root, parts[6])`, which interpolates the
*unvalidated* hash into a filesystem path:

    fn scv_parser_artifact_expected_path(root: text, hash: text) -> text:
        "{scv_parsers_dir(root)}/{hash}.wasm"

## Impact
Not exploitable as it stood: the constructed path is only ever compared for
equality against the recorded path, so a traversing hash still ended in a
rejection — but via the wrong branch, reporting "path" for what is a hash
defect. The guard ordering was nonetheless inverted relative to the fsck path,
the diagnostic was misleading, and any future use of the constructed path before
that equality check (e.g. a stat/read for a better error message) would have
turned this into a real parser-cache path traversal.

## Fix
Added the same `scv_object_ref_safe(parts[6], "sha256_")` check immediately
before path construction at both `parser_registry.spl` sites, emitting the same
`unsafe parser artifact hash:` wording `integrity.spl` already uses, and added
`scv_object_ref_safe` to that file's `std.scv.core` import. The two paths now
validate in the same order with the same message.
