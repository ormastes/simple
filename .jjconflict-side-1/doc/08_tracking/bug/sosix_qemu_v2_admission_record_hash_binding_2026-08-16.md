# SOSIX QEMU v2 admission record lacks manifest hash binding

Status: SOURCE FIXED / VERIFICATION OPEN — release-trust blocker

## Failure

The pre-fix collector v2 matrix manifest recorded
`admission_record_path_b64` but no `admission_record_sha256`. The adjacent
13-field `admission.env` could therefore be addressed by the manifest without
the manifest byte-binding the exact record consumed by a typed importer.

The preserved typed importer from commit `5958de7d4c7` cannot be reused: it
targets manifest v1, a 41-scalar admission record, and canonical 9/13 artifact
sets. Current direct-kernel v2 uses a 13-field admission record and eight
artifacts. That importer also returned from inside its manifest-line loop and
validated only the first line. The stale files were removed rather than
weakening release admission.

## 2026-08-16 source correction

The collector now hashes the exact written `admission.env`, emits
`admission_record_sha256`, and rechecks the record after the manifest append.
`src/os/sosix/qemu_evidence/trusted_importer.spl` consumes the complete 24-row
v2 wire, canonicalizes cell-relative paths and base64, binds admission and
evidence bytes, cross-checks identities, and validates canonical PASS artifact
sets. Its only release API accepts a collector root; the structural parser is
not re-exported as admission.

The structural parser and trusted importer also now parenthesize every
multiline boolean condition, initializer, return, and implicit result, as
required by the Simple grammar. This is a grammar-only correction: the exact
13-field admission record, 31-field row layout, 749-line manifest, canonical
row order, and hash bindings are unchanged.

Focused specs cover admission mutation, a malformed late row, and retained
artifact mutation. Each focused spec was attempted once with the deployed
self-hosted CLI and exited 139 before scenario output. A third bounded
diagnostic, `check src/os/sosix/qemu_evidence`, printed `Checking` and then
exited 139. No Rust seed or Stage-3 substitute was used. The current filesystem API also cannot hold an
fd-pinned snapshot across read/hash checks, so a hostile concurrent filesystem
can still race replacement between checks; the importer performs pre/post
regular-file/path/hash validation but does not claim to eliminate that TOCTOU.

## Remaining unblock contract

1. Run both v2 focused specs once on a source-matched admitted Stage-4 CLI.
2. Add behavioral path-escape/symlink sabotage coverage.
3. Introduce fd-pinned regular-file read/hash primitives, then use them for the
   manifest, admission, evidence, and retained artifact snapshots.
4. Keep the release gate restricted to the trusted collector-root importer.

## Exact resume

With a provenance-admitted Stage-4 CLI, run
`test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl` and
`test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl` once each. Do not use
Stage 3 or the Rust seed.
