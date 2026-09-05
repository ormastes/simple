<!-- codex-research -->
# Feature options: E-APACK008 forbidden-I/O enforcement

## Option A — Unified contextual and temporal enforcement (recommended)

Use E-APACK008 for both compile-time contextual rejection and runtime temporal
fail-closed enforcement. Static validation rejects canonical direct/transitive
acquisition from `@interrupt`, `@noalloc`, and `@realtime` call graphs. Runtime
enforcement seals lazy acquisition when the startup owner atomically publishes
the operational loader/catalog generation. Apply the policy only when
`lazy_io_after_start: deny` or the mission-critical profile enables it.

- Pros: matches the plan's safety intent; one diagnostic contract; covers both
  unsafe call context and post-startup timing; policy-off behavior stays
  explicit.
- Cons: requires stable resolved callable identities, a named transition owner,
  and static/runtime evidence; one code has two related trigger shapes.
- Effort: L after canonical identity exists.

## Option B — Split contextual and temporal diagnostics

Keep E-APACK008 for runtime post-seal acquisition and assign a new diagnostic
code to compile-time contextual reachability. Use the same policy activation
and operational publication event as Option A.

- Pros: diagnostics identify whether context or lifecycle timing failed;
  independent suppression and telemetry are clearer.
- Cons: diverges from the existing plan/code vocabulary; requires migration and
  permanent dual-code documentation and coverage.
- Effort: L after canonical identity exists, plus diagnostic migration.

## Option C — Contextual enforcement only

Reject forbidden acquisition from critical call graphs, but do not seal lazy
I/O after startup.

- Pros: smaller semantic/compiler implementation.
- Cons: does not meet the plan's post-operational zero-I/O requirement and
  leaves indirect/runtime acquisition unguarded.
- Effort: M after canonical identity exists; incomplete for the current plan.
