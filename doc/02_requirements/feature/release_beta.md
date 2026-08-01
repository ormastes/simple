# Release Beta Feature Requirements

Selected option: **B — Complete non-macOS beta release**.

- REQ-001: Produce a fresh strict Linux Stage 2→3→4 full CLI with stub fallback disabled.
- REQ-002: Qualify the exact Stage 4 CLI with essential test, lint, duplicate-check, and aggregate smoke markers.
- REQ-003: Validate every declared non-macOS release row: Linux x86_64/aarch64/riscv64, FreeBSD x86_64/x86, and Windows x86_64/aarch64.
- REQ-004: Run the canonical FreeBSD QEMU bootstrap check rather than treating host-only rejection as evidence.
- REQ-005: Validate executable roles, safe archive layout, notices, tracked font bytes, checksums, and MCP/LSP package identity.
- REQ-006: Require release jobs to fail closed when executable artifacts or payloads are absent; source-only substitution cannot satisfy an executable package role.
- REQ-007: Pass the release-bound whole interpreter suite and required compiler/core/lib/MCP/LSP gates on the fresh pure-Simple CLI.
- REQ-008: Prove a real GitHub Actions release workflow run succeeds before declaring the beta complete.
- REQ-009: Update release notes, changelog, scenario manual, design/process docs, and completion evidence before verification.
- REQ-010: Commit and tag only after `STATUS: PASS`; push only after explicit user authorization.

MacOS execution is excluded by the lane request, but retained macOS workflow syntax and dependencies must remain valid.
