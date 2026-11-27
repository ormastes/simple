# Extreme typing and traceability: current-source gap audit

Status: source review only, 2026-11-01. Reviewed release-lane base
`3273833de3dfe9ea8bc56d0cd877fa05bc1402db`; this is a new bounded review, not a
rerun of the supplied `97700b29e106` audit. No binary execution, performance
measurement, proof, or production-readiness qualification is claimed.

The [canonical traceability roadmap](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md)
retains REQ-TRC-001..020 and AC-TRC-001..040. Its historical audit and the
existing common graph are extended, not replaced. This proposal's open choices
are in [feature options](../../02_requirements/feature/extreme_typing_traceability_options.md).

## Findings and design consequences

| Current source locator | Source-supported finding | Consequence |
|---|---|---|
| `src/lib/common/traceability/model.spl:4`, `:30`, `:83` | Typed nodes, relationships and snapshot subjects already exist; Bug exists, dedicated group kinds and code/API facets are absent from these enums. | Extend common contracts and codecs; do not invent an app-owned graph. |
| `src/lib/common/traceability/schema.spl:179`, `:215` | Typed relationship endpoints and acceptance/nonacceptance role checks exist. | Preserve those distinctions when adding group, bug, code and API relationships. |
| `src/lib/common/traceability/query.spl:9`, `:48`, `:83`, `:95` | Snapshot is checked; one-hop queries rebuild maps and scan edges. Cursor binds generation/selected ID/direction, not limit or future filters. Returned edges are induced by page nodes. `complete` means page exhaustion. | Introduce indexed bounded traversal and a versioned cursor; graph completeness/qualification cannot be inferred from page exhaustion. Enumerate full graph edges separately from node pages. |
| `src/lib/common/traceability/graph_*_v1.spl`, `declarations_*_v1.spl`, `declarations_*_v2.spl` | Versioned graph/declaration formats already have owners. | Keep v1 readers and historical bytes; add explicit version dispatch and migration provenance. |
| `src/app/traceability/snapshot/git_provider.spl`, `git_tree.spl`, `extract/snapshot_pipeline.spl` | Immutable snapshot extraction has source implementations. | Reuse providers; execution and race handling remain test obligations. |
| `src/app/cli/command_registry.spl:218`; `src/app/traceability/cli_options_v1.spl:72`, `:92`, `:117` | Registry advertises `--format=text|json`; parser rejects obsolete flags and accepts SDN only. | Record as a concrete help/parser discrepancy; repair in P0 with a registry/parser contract spec. Proposed `simple trace` is not the current CLI. |
| `src/app/slop/session.spl:30`, `:55`, `:98`, `:144`; `projection.spl:1`; `view.spl`; `native_frame.spl` | Slop already consumes trace graph queries, checks snapshot identity and retains view state. | Extend the shared viewer, selection and native composition. Do not create a parallel Slop app. |
| `src/app/llm_caret/workbench/session_contract.spl` | Caret has its own session identity/lifecycle contract. | Consume registered worktrees through a read adapter; graph overlays must not own processes or lifecycle. |
| `src/compiler/35.semantics/lint/primitive_api.spl:55`, `:60`, `:85` | Legacy primitive checks compare flat type names and exempt homogeneous pure-math functions; check functions/fields across visibility levels. | Cannot satisfy canonical recursive external-surface enforcement. Private arithmetic remains legal under the proposed rule. |
| `src/compiler/35.semantics/lint/semantic_api/checker.spl:30..52` | Standalone text-based checker explicitly says it is not wired into live lint; covers all functions/private fields. Enum payload capture exists but is not routed into this checker. | Do not claim enum parser capture is absent or that recursive public API enforcement already runs. |
| `src/compiler/35.semantics/lint/semantic_api/type_walk.spl:145..193` | Alias/newunit handling and recursive type-text walking exist. Unresolved aliases can yield no leaves; generic traversal does not establish canonical base identity. | Reuse tests as negative fixtures, not the text walker as a type authority. Unknown must be explicit. |
| `src/compiler/00.common/api_surface_contract.spl`; `src/compiler/90.tools/api_surface.spl` | Existing manifests use text type names and signature collections. | E1 extends/reconciles this seam with canonical type identity and resolved effective visibility. It must not claim current manifests are sufficient. |
| `src/compiler/00.common/assurance/policy.spl`; `policy_schema.spl` | Shared raise-only policy resolution, V1/V2 policy types and verified-aware V2 entrypoints exist. | Extend one authoritative policy; audit adapters instead of building another profile table. |
| `src/compiler/80.driver/driver_safety_severity.spl:57..95`, `:124..154` | Robust intentionally warns; critical/verified deny; warning-phase can downgrade this projection. | New named extreme-API rule is fatal at robust+ without escalating every existing robust warning. Its denial cannot be bypassed by the old migration downgrade. |
| `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:186`, `:348`; `lint_checks.spl:397` | Lint configuration and warning-producing checks have distinct severity paths. | Gate parity requires call-chain and publication tests, not matching profile spellings alone. |

## Remaining research and admission blockers

The production visibility producer, resolved type graph, generated exports,
post-monomorphization exports and every execution engine need an E1 call-chain
audit. A visibility helper accepting only a Boolean is not evidence that explicit
private declarations and filename/module/reexport rules are resolved correctly.
No current-source observation here proves interpreter/JIT/loader enforcement.

The user subsequently selected the all-builtin catalog, domain-safe public
generic bounds and easy nominal type creation. Private FFI behind typed public
facades follows the selected no-public-primitive constraint. Group placement,
changeset identity, coverage roles and rollout choices remain open. Record
those before dependent implementation; no verify PASS is asserted.

The retained baseline `.spipe/simple_traceability_sdn_slop/resume.md` records
the prior user's full baseline scope/NFR selection and unexecuted 40 criteria.
Its missing integration/admission work is not erased by finding current source
provider modules. Source foundations are distinct from live qualified paths.

The retained knowledge receipt is
`.spipe/extreme_typing_traceability/knowledge_selection.sdn`. It records manual
registry routing for this documentation design; the selector was not executed.
Unrelated `.spipe/release_phase3_20261101/state.md` is outside this lane.
