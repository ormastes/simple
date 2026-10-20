# Canonical mold linker rejected by managed tool projection

Date: 2026-10-20

Status: focused source fix and regression scenarios authored; runtime **UNRUN**.
Bug database registration is pending a qualified pure-Simple CLI.

## Evidence and cause

The r16b Stage-2 `test_runner_build` receipt records status 1,
`artifact_status=producer-failed`, and `behavior_qualified=0`. Its log contains
56 `no C compiler available for empty module object` failures and 222 short
`llc not found` failures. Installed LLVM tools exist; those messages alone do
not establish host tool absence.

The task binds `target-managed-tools.env` with SHA-256
`be52680a9f70ecb9a54750d5fd8b52f01bca9b977e31b9cf3228f32771dc3215`.
Its linker row identifies `/usr/local/bin/mold` with digest
`7f5c75425b7afd1ab7faa987b7902ff0222f88b5e9dfb30e69e66a5ad3741fca`.
The producer in `scripts/check/lib/bootstrap-stage3/authority.shs` assigns
the requested `ld` the linker role, then records its canonical target.

`native_tool_role_matches_path_v1` omitted the canonical basename `mold`.
`native_tool_projection_decode_v1` validates all eight roles before creating
the owned bindings, so that row rejects the entire otherwise complete
projection with `managed tool projection role/path/digest invalid`.
The audited SCV source and captured remote
`30e9aa83e94f557137dbceae22b27973d125d625` have the same relevant source.

The LLVM helper's unconditional availability guard does not prove discovery
success. The short message comes from `compile_ir_to_object_path` after
`find_llc` returns an empty path. Both the LLVM and C discovery owners
translate strict resolver errors into empty paths.

This is a concrete producer/consumer mismatch. The historical first runtime
refusal remains unknown: scope, file metadata, or digest checks can fail
before projection decoding, and the retained error omits that detail.

## Selected correction and acceptance criteria

- **REQ-MOLD-001:** accept exactly the normalized basename `mold` for the
  linker role, allowing the canonical target already emitted by the producer.
- **REQ-MOLD-002:** keep other roles and unrelated or similar linker names
  rejected.
- **REQ-MOLD-003:** preserve full-manifest, digest, path, descriptor identity,
  ownership, and environment checks.

The implementation adds one exact comparison to the existing linker branch.
It adds no discovery, allocation, scan, fallback, or ownership changes.
Existing normalization of case and `.exe` is unchanged; this change supplies
no cross-host execution qualification.

Regression source:
`test/01_unit/compiler/backend/native_tool_authority_spec.spl`.
Manual:
`doc/06_spec/01_unit/compiler/backend/native_tool_authority_spec.md`.
The three new scenarios were authored before the production change.
All existing cases remain intact.

## Remaining work

Run the existing spec and relevant runtime checks only with a qualified
pure-Simple CLI. No compiler/build/retry was launched for this patch.
Runtime coverage, performance measurements, and successful linking are
unverified.

A separate diagnostic improvement should preserve strict resolver failure
details through LLVM/C discovery without weakening refusal or falling back
to ambient PATH. It is outside this patch. No claim is made that the r16b
campaign or all 278 failures are fixed.
