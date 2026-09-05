# Build/Test Abnormality Detection Design — TLDR

The implementation combines fixed resource classes, versioned runtime receipts, cohort-safe persistence, robust MAD comparisons, compiler spans, and explicit promotion without sharing live platform handles above the provider layer.

## Core Shape

- Linux: delegated cgroup/systemd exact-tree evidence with `wait4`/sampled/RLIMIT fallbacks.
- Tests/builds: shared scope, stable cohort identity, additive observations, and separate subject/run SDN records.
- Policy: absolute + relative + MAD floors, confirmation for failure, retained tails, gradual drift, complexity and retention probes.
- Runtime additions are limited to owner boundaries and document rejected exit-code/process shortcuts.

## Open Next

- [Full design](simple_build_test_abnormality_detection.md)
- [Architecture](../04_architecture/simple_build_test_abnormality_detection.md)
- [Operator guide](../07_guide/infra/simple_build_test_abnormality_detection.md)
