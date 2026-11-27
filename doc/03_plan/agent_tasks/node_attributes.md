# Node attributes: delivery ownership

2026-11-07 authorized pair update: Sol implements the broader accepted program
in bounded packages; Astra owns architecture/final source review; root/packaging
lands reviewed packages on release. The
[finite delivery matrix](../../08_tracking/data_attributes_program_progress_2026-11-07.md)
supersedes the historical no-parallel assignment below for this active session.
Canonical V1 remains frozen; the first new slice is the reviewed V2 extension
inside the existing `compiler.common.data` owner.

Date: 2026-11-06. Scope: full implementation, applied to Simple.

The primary Codex agent owns the integration branch, exact-head review and merge.
The implementation and PR base is `release/1.0.0`, as subsequently requested.
The architecture/design is carried from its main PR into the release branch
before structural implementation; unrelated release changes are preserved.
Lower-model sidecars: **N/A**; no parallel agent work has been requested. Final
review is by the primary normal-capability agent against source-matched evidence,
not acceptance of generated plans or test counts alone.

The user requested architecture/design to land first for sharing. Land L0 from
the [detail design](../../05_design/compiler/node_attributes.md) as a documentation
PR. L1 shared structural contracts precede consumer rewrites. L2–L6 continue toward
full support; none may redefine completion around a standalone contract/pilot.

| Lane | Owner | Inputs | Deliverable |
|---|---|---|---|
| L0 architecture/design | Primary | Saved plan and current source audit | Selected requirements, layer boundaries, detail design and test matrix, merged PR |
| L1 contracts | Primary | Reviewed L0 | Common schema/lifecycle resolver, opt-in context and focused negative tests |
| L2 Simple AST pilot | Primary | Landed L1 | Actual AST owner-backed generated construction/access and traversal |
| L3 language/engines | Primary | L1/L2 | SPL/SDN, HIR/MIR places, obligation checks and interpreter/native parity |
| L4 observations/tools | Primary | L3 | Get/set AOP, shared capture path, cache/LSP explanation |
| L5 Simple adoption | Primary | L3/L4 | AST/HIR/BuildRunner integration, off/on qualification and immutable receipts |
| L6 final audit | Primary reviewer | All prior executed evidence | Requirement-by-requirement verification and merged implementation PRs |

Contract names are defined in the detail design; scenario/helper names are defined
in the [system-test plan](../sys_test/node_attributes.md). Any future delegation
must retain those interfaces and explicitly assign disjoint files before work.

Current execution prerequisite: locate or produce an admitted pure-Simple runtime.
The audited Windows workspace has no demonstrated general-test runtime admission.
Resolve this through the canonical bootstrap workflow; do not substitute Rust seed
results. Architecture/design can land independently, labeled documentation-only.
