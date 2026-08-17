# Lint profile optional assertion runner failure — 2026-07-19

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

The focused lint-profile spec consistently reports 9 passing scenarios and one
failure in its existing `parse_lint_profile` optional assertions, while the new
invalid-CLI-profile scenario itself passes and returns exit 2. Attempts using
optional access, the nil matcher, and explicit nil comparison were not stable
under the temporary Rust-hosted interpreter. The three-cycle cap was reached;
fix the Option matcher/interpreter contract before changing this assertion
again.

## Re-verification 2026-08-17 (app-rest lane) — UNVERIFIED + path drift

Path drift proven: `src/app/io/cli_lint_commands.spl` contains ZERO references
to `parse_lint_profile`. The real subject is
`test/01_unit/compiler/lint/lint_profile_spec.spl:62-76` (the `.is_some()`
assertions, 17 `it` blocks).

Execution did not settle it: the one spec run returned `rc=143` with no
`Results:` line, which per lane convention is UNVERIFIED, not failed.
