<!-- codex-research -->
# Security Convention-First Architecture NFR

Selected NFR path: Option A.

NFR-001: Default convention inference shall be deterministic and not require full-tree scans beyond the source set already being checked.

NFR-002: Diagnostics shall be stable enough for tests to assert on diagnostic code, layer, feature, and required remediation fields.

NFR-003: The implementation shall preserve existing security diagnostics and HIR-based checks.

NFR-004: Focused compiler tests shall cover new coordinate inference and `SEC101` behavior.
