# Stage3 coordinator rejects its freshly encoded policy handoff

Status: OPEN; reproduced once on 2026-09-23. No production fix or Stage3 admission.

## Bound lineage and reproduction

- Frozen source: `42402d3468e13cfbaf48699c3071f70c647723db`, checkout `D:/b424fresh`.
- Admitted Stage2 compiler SHA-256: `510d70d22d0e909e04bb0f6e37087cea8c1fa1e0af6c8e89340db08b7168f7eb`.
- Parent receipt: `D:/b424fresh/build/bootstrap424/stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env`.
- Exact environment and command: `D:/b424fresh/build/native_probe/stage3-diagnostic424/run.sh`.
- Invoke that script with MSYS2 Bash. It runs the admitted compiler against `src/app/cli/bootstrap_main.spl`, LLVM/MSVC, `--mode dynload`, `--runtime-bundle core-c-bootstrap`, `--threads 12`, private cache, `SIMPLE_NO_STUB_FALLBACK=1`, and a 1800-second cap.

The source snapshot matched the admission snapshot before execution and remained unchanged afterward. This was an isolated diagnostic run: Phase2 had failed, and no canonical receipt was minted.

## Observed failure

Shell exit `1`, before object output:

```text
error: native-build could not create its internal policy handoff
```

No Stage3 compiler executable exists in the diagnostic lane. Stage4 was not started.

Evidence: `build.log`, `terminal.env`, `lineage.txt`, `parent-admission.env`, `source-before.txt`, and `source-after.txt` under the same diagnostic directory.

## Proven localization and remaining uncertainty

`src/app/cli/native_build_main.spl:734` calls `environment_variant_policy_handoff_attach_v1` after successful preparation. Its error at line 738 erases the typed cause. The attach owner (`src/app/cli/environment_variant_policy_handoff_owner_v1.spl:108`) decodes the freshly encoded payload and maps every decoder error to `InvalidInternalArgument`.

The exact rejection inside `environment_variant_policy_handoff_decode_v1` is unproven. Do not describe this as a filesystem failure: the handoff is an argument payload. Do not remove validation or switch the bootstrap to static provider bundling.

Existing regression surfaces are `test/01_unit/compiler/common/environment_variant_policy_handoff_v1_spec.spl` and `test/01_unit/app/cli/environment_variant_policy_handoff_owner_v1_spec.spl`. A direct-route owner probe failed on unrelated unresolved I/O facade names; a reduced pure-contract probe emitted unresolved-method const-zero warnings, so it cannot establish trustworthy decoder semantics. See `native_no_stub_mir_method_placeholder_exact424_2026-09-23.md`.

Resolution requires preserving useful typed rejection evidence, identifying the failed contract with a semantically valid focused executable, and then obtaining fresh source-matched admission before canonical Stage3/4 claims.

## Follow-up diagnostic checkpoint

The publication source now preserves typed construction, encoding, attach, and extract errors at the CLI boundary. A focused no-stub native probe passed malformed-payload reason checks, then its separate roundtrip fixture stopped with `policy-construction-failed:invalid-policy` before encode/decode. That fixture result does **not** identify the original exact424 attach rejection. The owner SSpec and canonical Stage3 have not passed on the changed source; a new source-matched admission is required before retrying Stage3.
