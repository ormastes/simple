# Layer Expert: Semantics Lint (`src/compiler/35.semantics/lint/`)

## Boundary rule

`35.semantics/lint/` owns the individual rule modules; `90.tools/lint/_LintMain/`
owns the driver that sequences them, maps codes to rule names, and attaches
EasyFix replacements. A new rule belongs in `35.semantics/lint/` as a pure
function over `(source, file_path) -> [Finding]`, exported from
`35.semantics/lint/__init__.spl`, and wired in exactly three places:

1. the module itself,
2. a `me check_<name>_spl(path, content)` plus its import in
   `_LintMain/lint_checks.spl`, called from the per-file check sequence,
3. the code→rule-name map in `_LintMain/config_and_model.spl`.

Rules in this layer use text heuristics over `iter_code_lines`
(`35.semantics/lint/lint_text.spl`), not the AST, so they run in
interpreter-mode specs ahead of full HIR/MIR lowering. Do not reach for HIR
from here.

`LintCategory` comes from `std.tooling.easy_fix.types` and currently has five
variants (Safety, Correctness, Warning, Style, Concurrency). There is no
`Performance` variant; a perf rule uses `Warning` rather than growing the enum.

## Review checks

- Lint cost is superlinear in file content and is gated by
  `sh scripts/check/check-lint-cost-budget.shs` (fail-closed). Measure any new
  rule's delta; do not batch multiple files into one lint invocation while
  iterating (use `sh scripts/check/lint-cached.shs <file>`).
- A new rule lands at `LintLevel.Warn` when the tree already carries offenders.
  Escalation to `Deny` is a separate, later change made only once the population
  is converted (`RAW-RT-00x`, `LEADOP001` precedent).
- Every rule ships both must-flag and must-NOT-flag fixtures.
- When a rule mirrors an existing `scripts/check/` ratchet, lift the ratchet's
  selftest fixtures into the spec so the two cannot drift apart silently.
