# SOSIX QEMU v2 admission record lacks manifest hash binding

Status: OPEN — release-trust blocker

## Failure

The current collector v2 matrix manifest records
`admission_record_path_b64` but no `admission_record_sha256`. The adjacent
13-field `admission.env` can therefore be addressed by the manifest without
the manifest byte-binding the exact record consumed by a typed importer.

The preserved typed importer from commit `5958de7d4c7` cannot be reused: it
targets manifest v1, a 41-scalar admission record, and canonical 9/13 artifact
sets. Current direct-kernel v2 uses a 13-field admission record and eight
artifacts. That importer also returned from inside its manifest-line loop and
validated only the first line. The stale files were removed rather than
weakening release admission.

## Unblock contract

1. The collector must publish the SHA-256 of the exact `admission.env` bytes in
   the immutable matrix manifest.
2. A v2 typed importer must canonicalize the collector root and relative
   admission path, require a regular non-escaping file, hash its exact bytes,
   compare the manifest claim, then parse the same bytes.
3. Tests must reject record mutation, path escape/symlink, missing/reordered
   fields, malformed base64, wrong artifact count, and a valid first row
   followed by a malformed later row.
4. The release gate must accept only the trusted importer result; structural
   caller-authored rows cannot cross the boundary.

## Exact resume

Update `scripts/check/collect-sosix-qemu-evidence.shs` and the v2 typed
`src/os/sosix/qemu_evidence/` model together, run their focused sabotage tests
once on a provenance-admitted Stage-4 CLI, then rerun the collector self-test.
Do not use Stage 3 or the Rust seed.
