# Provider snapshot digest filename and public regression helper

Owner: provider loader maintenance. State: source repair prepared; verification waiting.

`src/os/smf/provider_loader.spl`, in `provider_stage_artifact_snapshot_v1`, previously passed entire provider bytes to the hex encoder when building a snapshot filename. This makes the filename grow to twice the binary size. PR #7510 records a native Windows observation of a 142,336-character filename for a provider image and an atomic-write refusal. That historical execution is not independently reproduced here.

The original fix computes `blake3_hex(blake3_hash(bytes))` for naming, reuse, and staged-byte verification. It is preserved from commit `c1f283d65bd10ce4868ab2f90611f4dc5cc51443`. Its review identified a private cross-module import: the regression spec imports `provider_snapshot_content_id_v1`, but the owner did not export it. This follow-up adds that name to the existing public export list without changing the private-import baseline.

The real production-owner fixture stages 4096 bytes and checks the 64-character digest filename and byte readback. Adjacent cases retain SHA-256 pin refusal, original-path replacement, and planted-snapshot replacement. An explicit fixture-size assertion prevents an empty buffer from falsely satisfying the large-artifact scenario. The mirrored authored manual distinguishes the final source-shape assertion from runtime behavior.

Current-source SSpec execution, native admission, docgen, and performance evidence are NOT_RUN. Resume with `SIMPLE_LIB=src <admitted-cli> test test/01_unit/os/smf/provider_loader_snapshot_binding_spec.spl --mode=interpreter` and the applicable provider native/admission checks. Source landing does not close these verification obligations. The original PR branch is preserved until the reviewed replacement lands and supersession is documented.
