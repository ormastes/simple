# trace32_tools vendored cmm_lsp test-suite drift (2026-09-18)

Found by the 2026-09-18 whole-tree test sweep (submodule lane, macOS arm64,
seed binary). 12/21 `cmm_lsp/test_*.spl` print-tests pass; 9 fail with at
least four distinct root causes. These are ad-hoc print-test scripts (not
`*_spec.spl`), are not wired into any superproject push gate, and do not run
in CI. The vendored tree diverges from upstream
(github.com/ormastes/trace32_tools@main): the vendored copy carries extra
files (`test_case_path.spl`, `test_dialog_completion.spl`,
`tool_runner_*.spl`, `cmm_ast_json.spl`, `cmm_include_resolver.spl`,
`cmm_parser_runtime.spl`) that upstream does not have, while both sides share
an identical `CmmProgram { statements, file_path, errors }` (no `warnings`
field anywhere).

## Failure inventory (as observed 2026-09-18)

1. **test_case_path.spl — 13/17 fail.**
   - Dominant error: `semantic: function expects 1 argument(s), but more
     were provided` (exact callee not yet localized; needs a per-example
     bisect).
   - `resolve_file_reference normalizes backslash path` expects `true`, gets
     `false` — the vendored resolver does not normalize `\` to `/` (or the
     test input regressed).
2. **test_dialog_completion.spl — 3/3 fail.** Same arity-shape error family.
3. **test_check.spl (2/16), test_debug.spl (1/8), test_sample.spl (1/2),
   test_v4_fixes.spl (1 fail)** — CMM parse regressions:
   `if_else`, `local`, `entry`, `if_elif_else` statements report
   "Failed to parse statement". Possible genuine parser gaps on constructs
   the tests exercise; needs parser-lane triage.
4. **test_dbg2.spl — genuine infinite loop** (had to be killed by the
   sweep's per-test timeout).
5. **Fixture-layout drift**: `test_cli_conversion.spl` /
   `test_web_fixtures.spl` probe `cmm_lsp/test_fixtures/...` but the vendored
   pin keeps `test_fixtures/` at the trace32_tools root (same as upstream).

## Classification

Vendored-content drift from an in-flight lane, not a macOS/platform defect:
the same failures reproduce on the pristine origin/main worktree. Per
concurrent-lane rules these files are treated as another lane's debris —
preserved unmodified, reported here.

## Suggested next steps (for the owning lane)

- Localize the arity-mismatch callees in test_case_path.spl /
  test_dialog_completion.spl (compile with `--verbose-semantic` or bisect
  call sites against current std signatures).
- Decide whether `warnings` (or equivalent diagnostics) is a planned
  CmmProgram extension; if yes, implement in parser + vendored tests; if no,
  rewrite the two orphaned tests against `errors`.
- Triage the four parse regressions with reduced CMM inputs.
- Fix or quarantine test_dbg2.spl's infinite loop.
- Align fixture probing with the root-level `test_fixtures/` layout (or move
  fixtures under `cmm_lsp/` to match the scripts).
- Re-vendor from upstream or land the owning lane's parser work; the tree
  cannot stay half-merged.
