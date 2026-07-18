# SCV System Test Plan

Status: initial plan, 2026-05-14.

## Coverage

REQ-001, REQ-002: snapshot and restore preserve exact bytes, including same-size edits.

REQ-003, REQ-004, REQ-005: commits, changes, and operations record working-copy snapshots and views.

REQ-006, REQ-007: parse failures create private commits but do not promote to public-ready.

REQ-008, REQ-009: fallback parser works before Tree-sitter.

REQ-010, REQ-011, REQ-012: diff and merge start with raw/line behavior and store conflicts as data.

REQ-015: platform documentation includes x86-64, ARM64, and RISC-V compatibility language.

## First Specs

- `scv init` creates repository metadata.
- `scv snapshot` writes byte objects and operation log.
- Same-size content edits show modified status.
- `scv restore-op` restores exact file bytes.
- Unsupported text files receive fallback line parse entries.
- Binary files snapshot and restore as bytes.
- Parse errors remain private and block public-ready.
- Operation log can show prior views.
