# Shared traceability graph architecture

Status: implementation contract, 2026-10-03. Baseline source:
`88ecaa21054aea80eb7c8dd46052c344837fe78a`. No execution qualification claimed.

## Requirements and decision

Implement every requirement in
[selected requirements](../02_requirements/feature/simple_traceability_sdn_slop.md)
and the full [report](../09_report/simple_traceability_sdn_slop_final_2026-10-03.md).
The report remains the historical audit; current research records corrections.

One pure domain kernel in `src/lib/common/traceability` owns typed identity,
claims, resolution, obligations, evidence eligibility, incremental dependency
semantics and bounded read queries. Existing source, SSpec and DB owners supply
facts. `src/app/traceability` owns immutable snapshot adapters and side effects.
`src/app/slop` owns native session composition and view transforms.

The alternatives are independent app-specific graphs (rejected: divergent
claims), a single mutable authored graph (rejected: duplicate intent/observations),
and the selected reproducible materialized graph with attributable claims.

## Ownership and MDSOC

- Existing feature DB owns feature identity and authored lifecycle intent.
- Requirement documents and SSpec metadata own semantic obligations.
- Snapshot/source index owns existence, paths and qualified symbols.
- Versioned policy owns conventions; explicit declarations own exceptions.
- `RunnerTestDb` and its unified DB own observations; graph never writes a
  second authoritative result.
- Admission owns verified producer/artifact facts; candidate SDN cannot grant
  its own trust by setting `trusted: true`.
- Graph is disposable. Documentation and viewer are read-only projections.

Feature, layer, component/entity and transform are orthogonal dimensions.
Shared nodes have one identity and many memberships. Informational trace edges
do not grant cross-layer imports. The common kernel imports only pure shared
contracts/SDN; app adapters own Git, filesystem, environment, process, clock,
source reads and transaction publication. No GUI imports enter hook startup.

## Data and publication boundaries

The shared `std.common.sdn` codec is mandatory. Current canonical encoding
cannot embed tables in inline dicts/arrays. The v1 machine representation uses
one schema-marked dict with arrays of typed records; human tabular inputs may
be admitted only by a proven shared parser path. This is SDN, not JSON or a
custom line parser. Duplicate-key issues are errors.

Authored intent, extracted claims, resolved edges, actual observations and
qualification have separate record types. Conventional links establish targets,
never semantic acceptance or runtime execution. Unknown and incomplete are
explicit. Graph generations and run manifests publish atomically.

## Admission and threat boundary

Commit consumes index/SJ-frozen blobs. Push consumes every old/new/ref row.
Remote admission independently pins control plane, checker dependencies and
policy; candidate code is data during static checks. Real candidate tests run
in separate isolated execution. Missing subject, baseline, binary, budget or
evidence is exit 2/incomplete, never clean. Existing secret/conflict guards stay.

The current BASE-pinned manifest alone does not close executable/workflow
trust. Its replacement must prove candidate-no-op and policy-self-admission
negative fixtures. Full audits handle rule/schema changes and unknown closure.

## Incremental and performance design

Cache extracted facts by blob + extractor + grammar + schema/configuration.
Resolution dependencies include positive references, missing lookups, unique-ID
queries, membership/globs, policy, namespaces and evidence input scope. Reverse
dependencies expand an edit to affected obligations. Batch immutable object
reads; do not spawn per-file processes. Publication is generation-atomic.

Every incremental result must equal a same-input full rebuild including origins,
diagnostics and obligations. NFR targets are in the selected NFR document;
measure startup, request latency, peak RSS, closure size and warm/cold cache
behavior. No benchmark target is a measured PASS.

## Presentation and native viewer

Stable structural Markdown excludes mutable latest-run claims and self-containing
tree hashes. Immutable run reports carry actual source/input identities.
Static HTML and native Slop share projection/query results. Native viewer uses
real UITree/WidgetStore/UISession, a layered graph surface and accessible
relations; source slices are revision-pinned. See
[viewer design](../05_design/app/slop_viewer.md).

## Delivery and self-traceability

The development lane is itself a registered feature with the same REQ/AC IDs,
explicit links where irregular, actual execution evidence and review/PR links.
The full [acceptance plan](../03_plan/sys_test/simple_traceability_sdn_slop.md)
is mandatory. Parallel implementation is file-owned and parent-reviewed.
Release destination is `release/1.0` unless the user selects another line;
release policy and exact target evidence must be satisfied before integration.
No tag or package publication is implied.
