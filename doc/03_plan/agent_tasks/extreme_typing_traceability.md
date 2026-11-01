# Extreme typing and traceability: implementation and ownership plan

Status: design handoff, 2026-11-01. Selected no-public-primitives policy is in
[requirements](../../02_requirements/feature/extreme_typing_traceability.md).
This plan does not mark code, tests, proofs, deployed CLI or release complete.
The baseline [20-REQ/40-AC roadmap](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md)
and its outstanding implementation/admission work remain part of delivery.

## Incremental traceability PRs

| Phase | Concrete reviewable result | Dependencies and gate |
|---|---|---|
| P0 | `trace list/show` over existing node kinds; exact snapshot argument; help/parser consistency; table/SDN rendering | Baseline snapshot/provider integration and source-matched runtime required for execution claims. Preserve existing traceability-check. AC041 + existing AC002/010/011. |
| P1 | Authored group kinds, ID/membership schema, cycle detection and provenance migration | D1 selection; preserve v1 read. AC042 + AC026/027. |
| P2 | Forward/reverse index, walk/path/impact/gaps and complete cursor binding | P0; independent edge paging and fan-out limits. AC043/044. |
| P3 | Bug affects/reproduced_by/fixed_by declarations and views | D2 identity policy; no automatic fixed status from touched files. AC045. |
| P4 | Definition/observation/qualified coverage integration and new role table | D3 role policy plus existing trusted producer/artifact admission. AC021..028 remain mandatory. |
| P5 | Shared TraceViewProjection and CLI/LSP/MCP adapter parity | Extract common projection seam early in P0; full adapter PR after P2/P4. AC046. |
| P6 | Deterministic Markdown/HTML report projection | P5; explicit output, provenance, safe links. AC029..032/040/052. |
| P7 | Compiler symbol/code/API fact adapter with precise relation provenance | P0/P2 and compiler fact contract; may start before P3..P6 qualification work. AC047/054. |
| P8 | Sparse feature-layer membership and separate layer dependency matrices | P7; union counts, unknown dimensions, drilldown. AC048. |
| P9 | Existing Slop code/API/matrix views and inspector | P7/P8 and common projection; live capture/accessibility. AC033..037/049. |
| P10 | Immutable Git changesets and explicitly refreshed PR metadata | D2; offline unavailable semantics. AC050. |
| P11 | Caret registered-worktree semantic overlays | P9/P10; session generation, base/head/index/dirty capture, overlap honesty. AC051. |
| P12 | Export hardening, privacy and complete graph round-trip | P6/P9/P11; malicious content, private paths/prompts, independent edge pages. AC052/053. |

Early value path: P0 -> P1/P2 -> P7 -> P8 -> P9. P3/P4 evidence qualification
and P5/P6 adapters/reports can advance alongside it after their contracts are
defined. Early views must visibly remain unqualified when evidence is missing.
P7 does not wait for an unrelated full UI rewrite. P12 security requirements
apply from the first export; P12 is the complete adversarial admission gate.

## Extreme typing PRs and integrated milestones

| Phase | Concrete result | Exit gate |
|---|---|---|
| E0 | Record selected builtin/generic/private-FFI policy, catalog canonical identities, resolve remaining migration choice; source inventory of current callers/newunit ergonomics | No alternate public primitive allowlists; baseline compatibility impact documented. |
| E1 | Compiler-owned PublicSurfaceGraph, effective export closure, TypeIdentity/substitution/SCC walker and semantic-domain bound | No text-spelling authority; complete positions, unknown reasons, generated provenance; AC-EAPI-001..003/007. |
| E2 | Authoritative named policy and publication guard in first production engine; generated/postmono recheck | Deliberate-red robust denial before artifact/initializer; no global robust-warning escalation; AC-EAPI-004/005. |
| E3 | Easy newunit/typed literal/domain factory ergonomics and public API migration with typed private FFI facade | Actual declaration/literal execution and range/type failures; no raw generated constructor/getter escape; AC-EAPI-008/009. |
| E4 | Native/interpreter/REPL/dynload/JIT/SMF parity and policy-bound cache | Last-valid REPL, no denied initializer effects, no weaker-policy cache reuse; AC-EAPI-006/007. |
| T0 | Trace base CLI/groups/index and projections | P0..P2/P5 foundation; selected baseline trace tests retained. |
| T1 | Code/type/API trace facets | P7/P8 plus E1; trace consumes compiler facts, never duplicates checking. |
| T2 | Actual evidence/changeset linkage | P3/P4/P10; missing/stale/unsupported evidence remains incomplete. |
| U0 | Shared Slop inspection | P9 with E2 results; real visible-state captures. |
| U1 | Caret multi-agent registered overlays | P11, no lifecycle ownership transfer. |
| V0 | Production IR proofs where supported, perf receipts, full acceptance, release readiness | Unsupported proof targets blocked; all selected gates PASS before release proposal. |

E2 cannot be called complete while easy construction is unusable for the APIs
being migrated. E3 work can begin against E1 contracts and existing newunit
syntax in parallel with E2; avoid a forced period of unusable robust APIs.
Robust+ dependency crossings cannot use a package's weaker profile to bypass
the enforced external surface. Migration affects activation/order, not rule
exceptions. Trace work remains useful independently of final E4 parity.

## Work ownership and parallel interfaces

Primary design/final integration owner: parent Codex lane on `release/1.0.0`.
Architecture author: Astra. Final reviewer: highest-capability available normal
reviewer, independent of changed code. Lower-model sidecars: optional bounded
read-only source/test/link inventories; no authority to select policy, grant
qualification, mark coverage complete or accept generated manuals. No sidecar
production implementation is authorized by this documentation change alone.

Shared contracts are `PublicSurfaceGraph`, `TypeExposureWalker`,
`AssuranceRulePolicy`, `RobustApiChecker`, `PublicationGuard`,
`TraceSnapshotIndex`, `TraceQueryV2`, `TraceViewProjection`, `WorktreeOverlay`.
Implementation must reconcile names with existing owners before fan-out.
Suggested SSpec manual steps: `step("capture an immutable snapshot")`,
`step("inspect the selected requirement and its evidence")`,
`step("explain a rejected public API")`,
`step("compare registered worktree snapshots")`. Setup/check helpers:
`capture_trace_fixture`, `require_projection_subject`,
`compile_api_fixture`, `require_no_initializer_effect`,
`require_last_valid_repl`. Helpers must perform real work; temporary incomplete
ones explicitly fail. Do not submit empty/pass-todo placeholder specs.

## Every next PR's review and admission gates

1. Check lane/worktree ownership, consume the retained feature/layer receipt,
   name exact changed contracts and selected acceptance IDs. Preserve unrelated
   state and do not combine another session's changes.
2. Admit a source-matched pure-Simple self-hosted runtime and supported commands
   before execution claims. Current documentation-only review is not runtime
   admission; never use the Rust seed as a fallback for product verification.
3. Implement the smallest complete slice, meaningful negative cases and real
   SPipe steps. Generate mirrored Markdown manuals/captures only from executed
   specs, then manually review them. Keep executable specs under `test/`.
4. Run the slice's acceptance once, required compiler/lib/MCP/LSP checks for
   changed core surfaces, core runtime and MCP native smoke where applicable,
   and working/staged direct-env guards. Package smoke is required when package
   flow changes. Source-only evidence cannot substitute an unavailable gate.
5. Check no executable `_spec.spl` exists under `doc/06_spec`; review exact PR
   head and comments, resolve regressions, merge through the required PR flow.
   A merged documentation PR completes design delivery only.
6. Stop on convergence. At most six meaningful fix/verify cycles; do not rerun
   already-green checks without a changed implementation or new evidence.

Do not release until verify reports PASS across selected baseline and extension
obligations, source-matched deployed commands, perf and manual quality. Release
tags/publication need their separately required authorization; release must not
repair missing specs after verification. No release is performed by this plan.
