<!-- codex-design -->
# SPipe local knowledge setup agent plan

Date: 2026-09-08. Status: scoped implementation handoff, refined by Astra.

## Delivery order

1. Preserve the supplied research as a dated artifact and reconcile this design
   with current SPipe setup/resolver surfaces.
2. Implement first-user and project-clone interactive setup with the exact
   `.spipe/.spipe` user layout and project `.spipe` submodule layout.
3. Update common/organization/project wiki navigation and owner-focused
   company/project guides and skills.
4. Verify installation, repeatability, preservation, and scope/privacy fixtures.
5. Commit and push only owned changes using the user-authorized workflow.
6. Continue the hosted research/context-manifest and Slang cache waves after the
   setup delivery is complete; preserve their independent correctness gates.

## Assigned lanes and ownership

| Lane | Bounded responsibility | Files/contract |
|---|---|---|
| Astra design | Refine ownership, setup, maintenance, and acceptance contracts | This plan; architecture/detail-design/system-test-plan companions. |
| Setup implementer | Inspect existing installer, implement guarded initialization and compatible resolver storage | `SetupRequest`, `SetupInspection`, `SetupPlan`, `SetupReceipt`; actual owning setup module selected by integration. |
| Knowledge documentation | Common/organization/project indexes, LLM wiki, authoring guide/skill | Canonical documentation and provider integration surfaces only. |
| Verification | Local Git fixture execution, transcript evidence, preservation review | Shared SSpec/checker contracts in the test plan. |
| Integration | Resolve shared names, review patches, stage owned files, publish | Root agent; final review uses the best available model. |

Lower-model sidecar lanes: N/A for this bounded first delivery. The user
explicitly requested Astra refinement. Additional workers must receive a
non-overlapping file list and the shared contracts before starting; shared
indexes and registries retain one writer. Shared-file changes are returned as
proposals to integration rather than concurrent edits.

## Handoff invariants

The user-selected scope is documented as REQ-001 through REQ-008 in the
architecture. Use the manual step/helper names from the system-test plan.
Unimplemented test helpers fail explicitly with `assert(false)` or equivalent
failure; placeholders cannot be admitted as tests or completion evidence.

Inspection found the existing `.spipe/spipe` submodule dirty. Do not include its
unrelated changes, relocate it implicitly, or fold the repository's other dirty
feature lanes into this delivery. Existing common/resolver implementations have
priority over adding independently writable copies.

The primary merge owner reviews guide accuracy, generated-manual quality,
scope enforcement, migration behavior, and every claimed completion status.
No worker grants itself permission to publish private organization content.

## Following waves

| Wave | Work | Admission condition |
|---|---|---|
| Hosted research | Immutable source/coverage manifests, bounded DFS, structured results and adapters | Full workflow succeeds with no Slang installation. |
| Cache observations | Stable prompt rendering, usage normalization, content-based invalidation | Cached/missing/unknown observations remain truthful. |
| Learned ordering | Independent-task co-use, deterministic grouping, strictly >10% hysteresis | Held-out quality and observation/amortization gates. |
| Slang baseline | Capability/readiness audit, timing/memory, request isolation | Evidence of isolated cold/resident execution. |
| Slang exact reuse | Opaque snapshot/restore handles and suffix prefill | Cached/uncached parity and compatibility rejection. |
| Later storage | Paged state, leases, cancellation, tiers, distributed transport | Isolation, bounded resources, verified transfer benefit. |

The setup commit does not mark these following waves implemented. Record
remaining work against the supplied report and continue through their gates.
