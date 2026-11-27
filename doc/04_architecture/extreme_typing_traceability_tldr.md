# Extreme typing and traceability: TLDR

Proposed architecture, 2026-11-01; no runtime qualification. User-selected
robust+ policy forbids all bare builtin types in effectively external Simple
API, requires domain-safe public generic bounds and easy nominal construction.
Private representation is allowed; generated public raw constructors are not.

Compiler owns resolved `PublicSurfaceGraph`, `TypeExposureWalker`, named
`AssuranceRulePolicy` and `PublicationGuard`. Unknown blocks robust+; every
engine gates before publish/initializers and rechecks generated exports.

Extend `src/lib/common/traceability` and existing Slop. One pure
`TraceViewProjection` serves CLI/LSP/MCP/Slop/Caret/reports. Preserve v1 readers,
the 20 selected baseline requirements and 40 existing acceptance criteria.
Groups, bugs, compiler code/API facets and immutable Git/Caret overlays add
attributable facts, not another type or lifecycle authority.

Index once per immutable snapshot. Bind cursors to complete query shape and
visibility policy. Warm requests avoid scans/shell-outs. Invalidate on semantic
inputs, policy, absence and generated-surface changes. Sparse feature/layer
membership is separate from directed layer dependencies. Exports are offline,
explicit, deterministic and privacy-filtered.

Next: [architecture](extreme_typing_traceability.md),
[selected policy](../02_requirements/feature/extreme_typing_traceability.md),
[remaining choices](../02_requirements/feature/extreme_typing_traceability_options.md),
[phases and PR gates](../03_plan/agent_tasks/extreme_typing_traceability.md).
