<!-- codex-research -->
# Security Convention-First Architecture NFR Options

## Option A: Compiler Diagnostic Safety

Pros: Prioritizes correctness and low-risk compiler feedback.

Cons: Does not define runtime sandbox performance budgets.

Effort: S.

## Option B: Artifact Stability

Pros: Adds schemas suitable for tooling, CI, and generated reports.

Cons: Higher upfront design burden.

Effort: M.

## Option C: Runtime Enforcement Budgets

Pros: Prepares for sandbox/backend lowering and remote context runtime checks.

Cons: Premature for diagnostics-only slice.

Effort: M.
