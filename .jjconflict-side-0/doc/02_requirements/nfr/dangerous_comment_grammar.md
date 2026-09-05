<!-- codex-impl -->
# Dangerous Comment Grammar NFR Requirements

Date: 2026-04-23

## Selected Scope

The first rollout prioritizes compatibility, diagnostic visibility, and audit-quality rationale text for critical constructs.

## Requirements

- NFR-DCG-001: Existing Simple source shall continue compiling; unjustified constructs warn first.
- NFR-DCG-002: `bin/simple lint <path>` and the Rust lint stack shall surface required-comment diagnostics outside unit-only AST checks.
- NFR-DCG-003: Diagnostics shall include stable code, construct family, and an actionable canonical-form hint.
- NFR-DCG-004: Weak rationale checks shall reject empty text and obvious placeholders such as `todo`, `fix`, `later`, `because`, and `unknown`.
- NFR-DCG-005: Required-comment checks shall avoid new hot-path full-tree scans; file-backed lint checks operate on the current file content already being linted.
- NFR-DCG-006: Parser support shall preserve compatibility for bare `pass_*` and `case _:` during the warning migration window.
