# Executable Size Reduction - NFR Options

Codex options, 2026-04-23.

## Option A - Advisory Measurements

Print artifact sizes during release packaging without failing.

Pros: no release disruption. Cons: regressions are easy to miss. Effort: low.

## Option B - Failing Budgets

Fail when selected artifacts exceed documented byte budgets; skip missing artifacts only where a platform does not produce them.

Pros: prevents silent growth in CLI, MCP, LSP, native executable, and runtime archive outputs. Cons: budgets need maintenance as feature scope changes. Effort: medium.

## Option C - Budgets Plus Strip Enforcement

Use failing budgets and require packaged release executables to be stripped.

Pros: catches both size and symbol/debug leakage regressions. Cons: local debug builds must continue to use non-package paths. Effort: medium.

Selected: Option C, based on the user-provided implementation plan.
