# Isolated canonical-pass policy

Executable source: `test/01_unit/compiler/mono/mono_invocation_policy_v1_spec.spl`.

**8 authored scenarios; execution UNRUN.** This manually maintained companion groups related acceptance cases. Qualified SPipe generation, execution, coverage, native memory/performance and formal verification remain pending. Source review does not establish any of those results.

| Step | Action | Required observation |
|---|---|---|
| Reject invalid caller limits | Construct limits beyond each fixed verification ceiling. | Actual policy creation rejects before the canonical pass runs. |
| Keep one shared ledger | Reserve exact work then exhaust it while balancing nested traversal. | Failure remains sticky and depth balances. |
| Deduplicate canonical requests | Run the actual production worklist on repeated same-type calls. | Exactly one specialization is created. |
| Refuse partial publication | Request two concrete types with specialization cap one. | The second request refuses instead of publishing partial output. |
| Consume isolated pass once | Attempt a second invocation on the same isolated pass. | Reuse refuses; no previous output/cache is silently reused. |
| Validate actual declaration owners | Run an actual named module at a distinct source path through the canonical pass and completed-signature validator, then supply a conflicting row owner. | Exact path or logical-name authority succeeds; foreign owner refuses; ownerless local rows remain distinct from specialization placement requiring an explicit owner. |
| Stop collection rebuilding after failure | Rewrite three actual lowered literal expressions with one shared work unit, then compare ordinary and exact-three-unit controls. | One successful element is retained before failure; the failed and later elements are not pushed; sticky retry returns an empty rebuilt collection and depth balances. |
| Stop default-parameter rebuilding after failure | Rewrite an actual two-default function with two work units, exhausting the first default before rebuilding it. | Failure occurs before parameter push or environment binding; complete original function encoding and both parameters remain intact, and environment/depth restore. |
