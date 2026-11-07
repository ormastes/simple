# Provider snapshot binding

Executable source: `test/01_unit/os/smf/provider_loader_snapshot_binding_spec.spl`.

Status: authored manual; current-source runtime execution and docgen are **NOT_RUN**. PR #7510 reported historical execution, but this follow-up does not independently verify that report.

## Stage a bounded digest-named snapshot

Prepare an artifact and its SHA-256 admission pin. Invoke the production `provider_stage_artifact_snapshot_v1` owner. Check successful admission, a distinct snapshot path, and byte-for-byte readback. The 4096-byte fixture asserts its actual size before staging, then checks a 64-character content identifier and the exact digest-based filename. This exposes the old behavior that hex-encoded every artifact byte into the filename.

## Preserve the admitted bytes

After staging, replace the original artifact and read the snapshot again. Its bytes must still equal the admitted artifact, not the replacement. Supply a mismatched SHA-256 pin and check refusal with an empty load path. Plant different bytes under the expected snapshot name and check that staging replaces them with the admitted bytes. These controls exercise the real staging owner and filesystem; they do not establish isolation against every concurrent filesystem attack.

## Keep the native-open call bound to the snapshot

The final existing scenario checks source call spelling: `dynlib_open(staged.load_path)` must be present and `dynlib_open(request.artifact_path` absent. This is a static source guard, not evidence that a native library was loaded or executed.

## Verification waiting

Owner: provider loader maintenance. With an admitted self-hosted CLI, run `SIMPLE_LIB=src <admitted-cli> test test/01_unit/os/smf/provider_loader_snapshot_binding_spec.spl --mode=interpreter`, then the applicable provider native/admission smoke checks and docgen. Until those receipts exist, no current-source runtime, native-provider, performance, or release qualification is claimed.
