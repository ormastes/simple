# Executable Size Reduction - NFR Requirements

Codex final NFRs, 2026-04-23.

- NFR-001: Size checks must be deterministic shell checks with configurable byte budgets.
- NFR-002: Missing platform-specific artifacts may be skipped only when the caller explicitly passes `--skip-missing`.
- NFR-003: Packaged release executables under release/package directories must fail the check if reported as unstripped.
- NFR-004: The native linker must keep existing debug and fallback paths available for local diagnostics.
