# Sanitizer smoke must distinguish compilation, exclusions and execution

REQ-SAN-SMOKE-HONESTY: an unexpected runtime TU compilation failure must fail
the smoke command and retain its diagnostic. Explicit exclusions must name
their reason; allocation-harness execution must not imply project-runtime
execution. User authorized this bounded evidence-harness repair separately
from frozen Phase3 compiler candidate `ae2b2f13f792`.

The original smoke converted every compiler error to a platform skip and
overwrote `last_tu.log`. Its successful executable linked only a generated
allocation probe, yet the combined PASS implied that runtime code ran. An
observed run compiled 67 objects and skipped three: a Windows harness missing
`windows.h`, an optional WASM SDK shim, and a bare-metal include fragment.
Only the last diagnostic survived. This did not prove generic memory safety.

The smoke now retains relative-path object/log names (including duplicate
basenames), records fragment/project-header/optional-SDK/host exclusions in
`exclusions.tsv`, and fails any remaining compiler error. The generated
allocation probe and project object compilation have separate status rows.
No project runtime execution is claimed. Missing toolchains and zero eligible
objects remain SKIP, never memory PASS. Full-mode policy is unchanged.

Validation: `test/01_unit/scripts/sanitizer_smoke_reporting_test.shs` passed
once under WSL. Its controlled compiler tests unexpected TU failure, harness
build failure, preserved per-path diagnostics, duplicate basenames, explicit
fragment exclusion, and separated execution wording. This is a harness-policy
contract, not ASan or compiled-runtime evidence. The prior green real-ASan
allocation smoke was not rerun. Native generics and Phase3 qualification are
unaffected and remain separate gates.
