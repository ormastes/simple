# Release 1.0.0 memory hardening and MCP/LSP improvement

## Raw Request
$sp_dev do memory hardening and mcp lsp improve and land check already impled or not. go pherallel and land on release/1.0.0

## Task Type
feature

## Refined Goal
Audit and implement both user-selected Downloads plans against release/1.0.0, verify every requirement with authoritative evidence, and merge reviewed changes into release/1.0.0.

## Acceptance Criteria
- AC-1: Preserve both input plans byte-for-byte with hashes and map every requirement, acceptance row, formal obligation, and release gate to implementation and execution evidence; missing or indirect evidence remains open.
- AC-2: Complete the memory plan's ownership, short-borrow, cleanup, arena, cycle, pipeline, cache, hashing, process, budget, metrics, migration, and independent-gate requirements across its specified backend/host matrix.
- AC-3: Complete the MCP/LSP plan's provider, snapshot, session, source-view, help, annotation, diagnostic, debug, environment, change-analysis, protocol, edit-transaction, performance, and security requirements and acceptance gates.
- AC-4: Run applicable pure-Simple checks, real SPipe assertions and generated-manual review, runtime/MCP native smokes, performance evidence, direct-env guards, and full release-bound test gates once per unchanged criterion. No seed substitution or false PASS.
- AC-5: Update affected research, architecture, design, plans, doc/07_guide, doc/06_spec, feature/layer expert wiki, and bug records. Review skills/agent/command guidance for changed tooling contracts; record N/A only with specific reasons. Retain named owners and actionable unblock conditions for all outstanding evidence.
- AC-6: Review exact PR heads and comments, resolve regressions, and merge only this lane's verified work into release/1.0.0; preserve unrelated dirty work. No tags or publication are requested.

## Scope Exclusions
None from either selected plan. Incremental commits do not imply full goal completion.

## Cooperative Review
Parallel normal-capability lanes: memory_audit, mcp_lsp_audit, release_gates. Root owns integration and final review. Source ownership and shared interfaces will be fixed before parallel implementation. Existing canonical interfaces and manual helpers take precedence; new unresolved test oracles must fail explicitly. Root owns generated-manual review. Lower-model sidecars N/A: current agents perform evidence-sensitive audits directly.

## Phase
implementation-in-progress

## Log
- 2026-11-06: User selected both existing plans and parallel implementation; no new option selection inferred. Fetched origin/release/1.0.0 at e2ce7042552 and created isolated worktree. Original checkout remains untouched.

## Input integrity
- `simple_nogc_ownership_memory_hardening_plan.md`: SHA-256 `016c3718dfe49a9589f008609baee2196a4bce49d26238a7b95974cf2962c4d7`
- `simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md`: SHA-256 `72db8b8cc045ab51f31748684182583f370f08632e612764643cef69710b6021`

## Current evidence and ownership
- Baseline audits: `doc/08_tracking/audit/release100_memory_mcp_lsp_2026-11-06/` (source inspection, not execution PASS).
- memory_audit owns strict no-GC bypass policy propagation in compiler driver and focused tests/docs.
- mcp_lsp_audit owns empty-file/warning/path diagnostic truth and focused tests/docs.
- source_view owns new shared contracts/session/projection and source-open protocol wiring, with explicit unsupported capability boundaries.
- debug_truth owns shared-debug routing/fabrication removal after file-scope review.
- traceability owns the release100_memory_mcp_lsp requirement/design/plan documents.
- Root owns integration, final review and PR landing. Existing root checkout dirty work is outside scope.
- Release verification is pending an admitted full pure-Simple CLI. Stage2 admission permits only scoped compiler probes. Its full-CLI child failed on old source; the outer verifier continued standalone runner work. Neither establishes Stage4 qualification.

## 2026-11-06 implementation checkpoint
- Planning/input/audit PR #7233 merged at `92d4e0ed83f65157a6441f929aa29f66d090e7ed`; recovery clarification PR #7234 merged at `59c4af17045175701f6db8931a7c7a53274d556f` on release/1.0.0. These documentation merges close no product acceptance row.
- Implementation branch: `work/release100-hardening-implementation-20261106`. Strict no-GC bypass policy, diagnostics truth, debug unsupported receipts, and bounded L0 raw source route are authored with focused regressions/manuals/guides/wiki.
- Static peer review found no P0/P1 in these incremental changes. It found and resolved explicit byte-budget units, partial-diagnostic producer-status preservation, and the admission-to-eviction test seam. This is not execution evidence.
- Runtime tests and generated-manual qualification are NOT_RUN. One diagnostic attempt with the unadmitted deployed binary failed before running tests in existing bounded_bytes syntax; it is not PASS and will not be used as fallback.
- Freeze this source for an isolated canonical pure-parent bootstrap prerequisite. No source edits during the active frozen build. Retain failed receipts and caches; the goal stays active and the full selected plans remain open.
