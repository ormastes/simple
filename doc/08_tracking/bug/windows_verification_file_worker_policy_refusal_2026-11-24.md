# Windows verification scheduled an impossible file-worker pool

Status: policy repair; native full-CLI and runner qualification still pending.

The admitted LLVM Phase2 compiler from release source
`f6f7d0abcdc42e77f91e589c1024bd1403069f5f`, SHA-256
`7ca285e94a7ada395194b1e483d4c7c60909d5d84e6651e322562b877df70c74`, passed
canonical Hello, struct receiver and positional Stage3-route checks. Its normal
slim verification campaign then failed both tool builds before linking.

The CLI parsed 4,136 modules in 154 seconds; its coordinator peaked at
3,855,956 KiB. The runner failed after 66 seconds. The campaign admitted a
15,636,440 KiB owner, but its small-host plan requested one worker and the
Windows product policy independently capped the frontend at 3,000,000 KiB.
The compiler correctly refused `hir_workers=0 mir_workers=0, need >= 2`.
Neither tool was published and no test execution is claimed. Original evidence:
`C:/simple-bootstrap-llvm-20261123/output-sdk-fix/stage2-compiler-tests/x86_64-pc-windows-gnu/verification/`.

The repaired Windows per-file policy uses the admitted owner share. When an
automatic whole-build plan fits one historical whole-closure worker, an existing
request for at least two may instead use two module-scoped unit workers under
a 10 GiB enforced cap. This requires the old cap already to cover 10 GiB and
raw measured available memory minus the configured reserve to cover 10 GiB.
The measured coordinator plus two 3 GiB unit floors motivate that admission;
the compiler's live worker admission and process-tree guard remain authoritative.
Explicit caps, explicit one-worker requests and the two-pass route are unchanged.
Impossible PhaseC worker counts or Windows shares fail before compiler launch.

`scripts/bootstrap/tests/windows-verification-file-worker-policy-test.shs`
exercises the production planner, share transport and early refusal with explicit
OS-memory sensor fixtures. It performs no compiler build and makes no native
qualification claim. Existing rejected campaign evidence remains retained.
