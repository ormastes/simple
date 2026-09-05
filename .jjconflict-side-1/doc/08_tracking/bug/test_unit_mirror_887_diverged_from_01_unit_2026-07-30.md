# Bug: `test/unit/` is a drifting mirror of `test/01_unit/` — 887 diverged files, all still executed by the default scan

- **Date:** 2026-07-30
- **Severity:** medium (structural — stale spec copies run in every full suite; fixes land in `01_unit` and silently don't apply to the mirror)
- **Area:** test tree layout / test runner scan root
- **Found by:** lane SPD1 (mission-critical robustness campaign), following lane LEXD's single-file finding.

## Numbers (2026-07-30 scan)

- `test/unit/`: 8,309 files; `test/01_unit/`: 14,654 files.
- Same-relative-path pairs: 8,291 (the other 18 are stale generated
  artifacts unique to `test/unit`: `.jit.note.sdn`, `summary.txt`).
- Byte-identical: 7,404 (89.3%). **Diverged: 887 (10.7%)** — 878
  `_spec.spl`, 9 `_test.*`.
- `bin/simple test`'s default scan root is `test/` recursive, so BOTH
  copies of every pair execute — diverged mirror copies run stale
  assertions (or fail outright: `inline_asm_core_parser_spec.spl` was
  6/10 in the mirror vs 10/10 in `01_unit` until reconciled this date).

## Caveat before acting in bulk

A sample of diverged pairs shares the same last git commit hash on both
sides — some "divergence" is concurrent uncommitted working-tree edits
from parallel lanes, not long-standing drift. Re-scan on a clean checkout
of origin/main before deciding a bulk policy. Ranked lists preserved in
the SPD1 lane report (top offenders: browser_session_fetch_wasm_chain,
browser_session, isel_riscv32/64, simple_web_renderer).

## Fix direction (needs a policy decision — orchestrator/user)

Either delete the `test/unit/` mirror entirely (after porting any
content genuinely newer on that side), or exclude it from the default
scan root, or make it a symlink. Until then: any spec repair applied
under `test/01_unit/` MUST check for and port to a `test/unit/` twin.
