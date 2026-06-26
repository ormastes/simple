# Domain Research: Warning/Allow Root-Cause Cleanup

## General Guidance Applied

- Make one warnings-as-errors lane authoritative before deleting suppressions.
- Prefer fixing lint false-positive boundaries over adding or retaining blanket
  `allow` annotations.
- Keep preview, editor, and platform-exploration lanes advisory until the owned
  signal is stable enough to avoid blocking unrelated work.

## Applied To This Repo

- Rust: the authoritative lane is strict Clippy over the real workspace at
  `src/compiler_rust/`.
- Simple: the authoritative lane should start with stable code-quality canaries
  under `test/code_quality/` and only expand after noise is measured down.
- Annotation/decorator linting must keep its whitelist aligned with language
  features used by the stdlib so that suppression removal does not regress
  legitimate syntax.
