# Preserve Hello evidence across watchdog termination

The phase 2 candidate `555e5515fe336b55ae9db2fdeced49a48f85890e6615edc68b83a1682fd72eae` exceeded the RSS cap in both Hello backend gates. The gate's TERM/EXIT cleanup deleted the internal candidate logs, leaving only the outer watchdog receipt. A separate diagnostic invocation was needed to discover the compiler's last reached boundary.

`check-stage2-hello-world-native-build.shs` now accepts optional `HW_ARTIFACT_DIR`, an existing absolute directory owned by the caller. Each actual candidate gets a fresh child directory printed as `ARTIFACTS <path>`. Its build logs, cache and output executables are written directly there and excluded from both immediate and trap cleanup. This preserves evidence without relying on a signal handler copying files before SIGKILL. The caller owns cleanup and disk budgeting.

Without the setting, temporary cleanup remains unchanged. Selftests always use their own temporary owner, even when the caller requests retention. The candidate verdict, timeout, backend and two argument-form contracts are unchanged. Retained files do not constitute a successful compiler admission.

The gate selftest checks ordinary cleanup and retained diagnostic/output files while preserving the same two-arm verdict. Actual compiler memory exhaustion remains unresolved; this change only repairs evidence retention.

Validation: `sh -n` passed and the actual gate `--selftest` reported eight passing cases. A separate process-level test launched this gate with an instrumented shell candidate, waited for its diagnostic in the retained entry log, sent TERM and KILL to the owned process group, reaped it with a nonzero exit and confirmed that the diagnostic survived. This exercises the wrapper's signal/evidence contract, not a real compiler. Artifact directory: `/var/tmp/item5-hello-retention-check-20261006`; driver recipes: `D:/dev/simple/build/review/item5-hello-retention-fixture-check.sh` and `item5-hello-retention-signal.py`. The first isolated harness attempt stopped before selftests because its copied fixture used the obsolete path; copying the current `test/04_smoke/bootstrap_hello_world.spl` fixed the harness setup.

Usage: create a caller-owned absolute evidence directory, then set `HW_ARTIFACT_DIR` to it while invoking the normal gate and watchdog. No new attempt of the failed phase 2 compiler was run for this wrapper change.
