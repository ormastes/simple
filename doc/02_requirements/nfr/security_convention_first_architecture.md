<!-- codex-research -->
# Security Convention-First Architecture NFR

Selected NFR path: Option A.

NFR-001: Default convention inference shall be deterministic and not require full-tree scans beyond the source set already being checked.

NFR-002: Diagnostics shall be stable enough for tests to assert on diagnostic code, layer, feature, and required remediation fields.

NFR-003: The implementation shall preserve existing security diagnostics and HIR-based checks.

NFR-004: Focused compiler tests shall cover new coordinate inference and `SEC101` behavior.
## 2026-05-23 Live KMS CI Hardening NFR Addendum

NFR-LKMS-CI-001: The live workflow checker must run without cloud credentials and without requiring network access.

NFR-LKMS-CI-002: The checker may use `actionlint` when available, but the default repo hygiene path must not depend on installing a new external tool.

NFR-LKMS-CI-003: The manual live KMS workflow must keep minimum default GitHub token permissions.

NFR-LKMS-CI-004: Documentation must distinguish hermetic CI from manually approved credentialed live-provider validation.
