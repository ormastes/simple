# Phase-C tool builds run with per-process producer identity (ABI receipt never passed)

- Filed: 2026-11-26
- Status: FIXED (this change)
- Found by: release/1.0.0 stage2 compiler-test matrix, lane v6
  (`compiler_cli_build` TIMEOUT after 14401 s, pinned e803fa9762cd)

## Symptom

`compiler_cli_build` hit its 14400 s row timeout having lowered 911 of 4159
modules (~16 s/module, one unit child at a time). Every unit logged:

```
[native-build] no ABI admission and no stable compiler identity
  (per-process:half-claimed-admission); native object cache is per-process this run
```

## Root cause

`bootstrap-phase-verification.shs` sets `SIMPLE_ABI_POLICY=v1` for the phase-C
tool rows but never sets `SIMPLE_ABI_ADMISSION_RECEIPT`.
`native_build_unadmitted_identity_decision_v1`
(`src/compiler/80.driver/driver_build/incremental.spl`) treats exactly one of
the two variables as a half-made claim and falls back to a per-process
`uncacheable-abi-admission-<pid>-<micros>` producer identity. Consequences:

- every per-file unit child gets its own object-cache scope, so no unit reuses
  another unit's objects (the cli and runner closures share most of src/lib);
- reruns start cold even though `SIMPLE_NATIVE_BUILD_CACHE_DIR` persists;
- combined with the strict managed-tool serial codegen lane and a
  free-memory-derived `build_threads=2` (one thread per tool build), the
  full-CLI row needs ~18 h against its 14400 s timeout.

The stage3 lanes already pass the receipt
(`scripts/bootstrap/lib/stage3-native-build-worker.sh`,
`scripts/bootstrap/resume-stage3-from-admitted.sh`); the verification rows
were the only consumers left on the half-claimed identity.

## Fix

- `bootstrap-phase-verification.shs`: export
  `SIMPLE_ABI_ADMISSION_RECEIPT=$(dirname "$compiler")/admission.env` for the
  tool rows when the admitted stage2 receipt exists (it is validated by
  `validate_phase_c_tool_binding`; its `candidate_sha256` equals the compiler
  snapshot's hash, so `native_build_admitted_abi_identity` admits it).
- `phase-c-backend-commands.shs`: add `SIMPLE_ABI_ADMISSION_RECEIPT` to
  `bootstrap_phase_c_tool_row_environment_keys` so the exact-environment row
  launcher (`env -i`) does not strip it.

With the receipt, the producer identity is the stable admitted one
(`policy=v1;...;receipt-sha256=...`): unit children share object scopes, and
reruns reuse the persistent per-tool caches.

## Note on lane configuration

Lane v6 also derived `build_threads=2` (free-memory/3 GiB at matrix start),
halving the designed per-tool parallelism (2 threads per build at the default
4). On hosts where the derivation under-measures, set
`BOOTSTRAP_VERIFY_BUILD_THREADS` explicitly — the from-scratch wrapper
documents it as a deliberate override.
