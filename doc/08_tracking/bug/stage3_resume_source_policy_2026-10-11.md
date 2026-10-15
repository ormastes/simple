# Stage3 resume loses authenticated source policy

Status: OPEN. Severity: P1. GitHub: https://github.com/ormastes/simple/issues/3114.
Canonical ID: `BUG-STAGE3-RESUME-SOURCE-POLICY-20261011`.

This inherited defect was independently identified in candidate tree
`9a95f2ae00ec3080ef9bbfaf9508e8a8d4fc2c56`. The resume wrapper reconstructs
Stage2 transcript argv at lines 450–456 and authenticates its argument digest
through parent admission at lines 553–559. Its Stage3 argument digest at
lines 866–895 and worker command at lines 99–102 then omit all explicit
sources and entry-closure policy. Default source discovery can replace
selected K1, disabled/dynamic CUDA and plugin overlays, and change the
entry-closure versus all-objects compilation policy.

The source repair extracts only ordered `--source` pairs and optional
`--entry-closure` from the authenticated in-memory Stage2 argv. The same
vector enters the Stage3 digest, all four worker launches, and the actual
compiler command. Missing explicit roots, malformed options and invalid
trailing worker policy refuse rather than discover defaults. The existing
29 typed fields, RSS and ABI checks, and source-before/source-after guards
remain in place. No ambient manifest selects replacement roots.

Six source-only controls in
`scripts/bootstrap/tests/stage3-source-policy-test.py` passed once: exact
order/optional closure, malformed refusal, production reconstruction,
production digest/worker argv equality, all four launch branches, and
worker prefix policy/RSS validation. Shell syntax checks also passed.
These use shell recorder functions and do not invoke a compiler.

Two existing direct-worker fixtures were adapted for the source-policy tail
and helper, also correcting their inherited missing typed RSS argument.
Both changed fixtures now PASS with shell recorders and exact-base
prerequisites. The inherited HIR extractor defect is repaired and tracked
separately in #3116; its negative real-engine boundary mutation refuses.
The ABI fixture validates the transcript owner's single positive reserved
budget row before comparing the original env/argv vector, with four refusal
controls. Six original policy controls were not rerun.

Independent source review remains required. Native/build/runtime
qualification is UNEXECUTED; no Stage3 admission or release PASS is claimed.
The bug remains OPEN until corrected-producer native qualification is
completed. Database registration is owned by the final composition lane.
