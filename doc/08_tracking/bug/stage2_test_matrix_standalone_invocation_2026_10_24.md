# Standalone stage2 compiler-test matrix invocation (2026-10-24)

How to re-run the mandatory Stage 2 compiler-test matrix against an admitted
Stage 2 candidate WITHOUT a full `bootstrap-from-scratch` lane — needed when
the lane's test phase must be retried (e.g. heap-luck crash retry) before a
managed resume accepts the receipt.

Discovered empirically; each gate below was a real refusal in order.

## Recipe

```sh
CAND=<bootstrap-output>/stage3/<platform>/stage2-admitted/simple.exe
SHA=$(sha256sum "$CAND" | cut -d' ' -f1)
T=<bootstrap-output>/stage2-compiler-tests/<platform>
rm -f "$T/rejection.env" "$T/stage2-compiler-tests.env"   # 5

export SIMPLE_WINDOWS_ABI=msvc                 # lane selector (or mingw env)
export BOOTSTRAP_STAGE2_TEST_DELEGATE=0        # 2: in-process rows; no MC/DC waiver
export BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT=1800
export BOOTSTRAP_STAGE3_FACADE_PATH=<repo>/scripts/check/lib/bootstrap-stage3-provenance.shs

sh scripts/bootstrap/bootstrap-phase-verification.shs \
  --phase=stage2 --backend=llvm \
  --compiler="$CAND" --compiler-sha256="$SHA" \
  --strategy=normal --profile=slim --hash-policy=canonical \
  --work-root="$T/verification" --cache-root="$T/cache" \
  --source-root=<repo> --timeout-seconds=7200
```

On exit 0, publish the PASS receipt (the managed resume verifies it):

```sh
sh scripts/bootstrap/lib/verify-stage2-compiler-tests.shs --publish \
  <bootstrap-output-abs> <platform> "$CAND" "$SHA" <repo> \
  "$T/verification/summary.env" <log>

sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-managed-from-admitted=<bootstrap-output> \
  --bootstrap-receipt=<bootstrap-output>/managed-stage4-planner-admission-v2.env
```

## The five gates (verbatim refusals, in order)

1. `missing Stage 2 admission` — the `--compiler` must be the ADMITTED copy
   (`stage3/<platform>/stage2-admitted/simple.exe`), whose directory carries
   `admission.env` + `runtime-capsule.env` (phase2-runtime-binding.shs reads
   them beside the binary). The `stage2/<platform>/simple.exe` copy refuses.
2. `delegated rows run MC/DC off and need SIMPLE_MCDC_OFF_WAIVER_REASON ...`
   — default `BOOTSTRAP_STAGE2_TEST_DELEGATE=1` demands a four-variable
   waiver. The lane sets `=0` (in-process rows); no waiver needed.
3. (worker) `BLOCKED exit=-2 claimed=0` mid-promote — the per-row internal
   native-build timeout default (600s) kills the HIR shard worker during
   `rt_transient_heap_promote`'s retain scan. `BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT=1800` matches the lane.
4. `BOOTSTRAP_STAGE3_FACADE_PATH: unbound variable` (authority.shs) — export
   it to `scripts/check/lib/bootstrap-stage3-provenance.shs`.
5. `retained compiler-test rejection blocks managed resume` /
   `compiler-test PASS receipt unavailable` — clear BOTH
   `stage2-compiler-tests/<platform>/rejection.env` and any stale
   `stage2-compiler-tests.env` before re-running; the resume path only
   VERIFIES an existing PASS receipt, it does not run the matrix.

## Resume-command form

`--resume-managed-from-admitted` is strict: EXACTLY two args
(`--resume-managed-from-admitted=OUT --bootstrap-receipt=ENV`); extra flags
like `--jobs` exit 2 with `requires one --bootstrap-receipt planner authority`.
