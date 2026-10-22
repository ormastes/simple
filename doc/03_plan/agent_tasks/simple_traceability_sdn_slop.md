# Parallel delivery ownership

Baseline: `88ecaa21054aea80eb7c8dd46052c344837fe78a`.
Full scope: report WP0..WP7 and REQ-TRC-001..020; no partial slice is completion.
Shared interfaces: `doc/05_design/simple_traceability_sdn_slop.md`.

| Lane | Owner | Exclusive write ownership | Review/next dependency |
|---|---|---|---|
| Kernel | Astra | common/traceability model/schema/codec/resolve/conventions/query; focused kernel unit specs | Root integration, later independent acceptance review |
| Evidence | acceptance_inventory | common/traceability evidence_model/evidence/obligations/markdown; evidence unit/scenario specs | Astra structural-model contract, root runner adapter |
| Viewer | viewer_design | src/app/slop; Slop unit specs and UI design | Shared query contract; root central CLI registration |
| Integration | root | snapshots, gates, extraction, incremental store, runner registration, CLI routing, self-trace records, requirements/architecture/detail docs | Consume reviewed lane APIs; serial runtime checks |

Current lower-model sidecar: GPT-6 Luna owns frozen-plan reconciliation and
runner transport integration; root reviews and integrates, with Astra's
independent source review. Historical lane assignments above describe the
original checkpoint and do not claim those sessions are currently live.
Merge owner: root. Final architecture/contract reviewer: Astra. Generated-manual
review: acceptance lane plus root operator reading. Runtime execution: root only,
serialized to protect the test DB. Branch landing: root only.

## Full dependency plan

1. WP0: source/settings/runtime provenance, baseline measurements, primary-source
   re-research, trust/control-plane route and supported-host plan.
2. WP1: typed model/SDN round trips and rejection fixtures, schema ownership.
3. WP2: real source/SSpec/DB adapters, authority/conventions, explicit exceptions.
4. WP3: exact index/ref/SJ snapshots, dependency-aware incremental store, short
   local dispatcher and independently trusted remote control-plane integration.
5. WP4: runner-owned immutable plan/observations, provenance validation, formal
   sidecar migration, truthful automatic feature-run SDN/Markdown.
6. WP5: deterministic structural and immutable run projections, static/offline
   HTML, ownership-safe publication and security/visibility tests.
7. WP6: actual native three-pane Slop, real interaction/capture evidence,
   revision-pinned source, accessible relationship view and delta recovery.
8. WP7: architecture/design/dependency projections and preserved distributed
   evidence adapter seams without claiming deployment of a distributed DB.
9. Full matrix, current-host and other supported-host evidence, NFR samples,
   guide/manual/skill freshness, self-traceability and exact release PR landing.

Shared manual steps and helper names are frozen in detail design. Missing
adapters fail explicitly. Each task reports authored/inspected/executed states
separately. No skipped/placeholder acceptance can authorize release.

## Runtime prerequisite

An admitted source-matched Stage 4 binary has not yet been located. The Windows
wrapper can select Rust; it is not a permitted verifier. Source implementation
may proceed, but compilation/test/docgen/benchmark PASS and release admission
remain unproven until exact runtime provenance is supplied or built by its
authorized owner. No other agent's build is restarted or claimed as this lane.

## 2026-10-11 current assignments and handoff

Root owns scoped snapshot composition, exact-snapshot CLI preview, input
identity, self-trace declarations and integration. Luna implemented the pure
run-plan reconciler, transport-presence helper and runner persistence ordering.
Astra appended current research/design corrections and reviewed those source
changes. Its content-collision, empty-plan/scope and missing-transport findings
were fixed. A later selector review found `git:index` confused with staged
selection; explicit snapshot kind now distinguishes them, with an authored
production parser regression.

Resource cleanup was a separate read-only ownership audit; no unsafe cache or
active build deletion was used to unblock qualification. All new native specs,
the SDN declaration parse and complete feature acceptance remain unexecuted.
