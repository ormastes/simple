# Lint profile optional assertion runner failure — 2026-07-19

**Status:** REPRODUCED / OPEN

The focused lint-profile spec consistently reports 9 passing scenarios and one
failure in its existing `parse_lint_profile` optional assertions, while the new
invalid-CLI-profile scenario itself passes and returns exit 2. Attempts using
optional access, the nil matcher, and explicit nil comparison were not stable
under the temporary Rust-hosted interpreter. The three-cycle cap was reached;
fix the Option matcher/interpreter contract before changing this assertion
again.
