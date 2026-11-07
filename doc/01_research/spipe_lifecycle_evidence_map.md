# Lifecycle completion evidence map

Status: research only; requirements selection pending. None of the proposed lifecycle criteria is proven complete by this map. Scope follows the full [proposal](../04_architecture/spipe_complete_lifecycle.md), including M0–M6, rather than treating an inventory tool as the destination.

## Acceptance evidence

| Proposal criterion | Authoritative proof required | Current evidence / missing work |
| --- | --- | --- |
| 1. Bidirectional feature-to-release trace | Real feature run, stable IDs, exact build/release identity, forward/back queries, broken/orphan-link negative fixtures | Existing review/release contracts provide identity fields; lifecycle trace graph and complete run unverified |
| 2. Negative acceptance before test-ready | Transition rejects a hardening scenario without negative coverage; authorized waiver is visible and expires | Lifecycle transition and waiver implementation missing from inspected surfaces |
| 3. Missing/stale binary fails closed | Execute missing/stale/wrong-revision fixtures; receipt pins executable digest, source, environment and selector | Simple CLI rejects unported operations; this does not prove lifecycle test receipt behavior |
| 4. Complete P1 incident | Sanitized historical incident capsule with dump manifest, hypothesis/reproduction, prevention, recovery receipts and reviewed lesson | Incident adapters, manifests and end-to-end evidence unverified |
| 5. Wiki archival with provenance | Duplicate/false strategy evaluation, approved archive, redirect resolution, default retrieval exclusion, retained history | Existing knowledge contract supplies ownership/invalidation policy; executable curation behavior unverified |
| 6. Enforceable rules | Positive and adversarial fixtures for every new rule plus proof relevant phase invokes the guard | Existing generated guidance checker is reusable infrastructure; lifecycle rule invocation and fixtures missing |
| 7. Frozen model evaluation | Blinded root-cause-family split, exact skill/wiki/model hashes, repeated large/small trials, cost/latency/safety/solve metrics | Fine-tune guides and attempt records exist; matched lifecycle replay and leakage controls unverified |
| 8. Authorization before discovery | Instrumented denial before filesystem read, index lookup or cached retrieval, including named private paths | Normative knowledge policy explicitly requires authorization before discovery/read/export/cache; enforcement across new tools remains to prove |
| 9. Equivalent canonical validation | Same valid/invalid golden inputs through Claude/Codex/Gemini adapters, Node/Simple CLI, MCP and CI | Existing Node core/adapter split and plugin equality checks are reusable; Simple migration is partial |
| 10. Incremental efficiency | Pinned realistic fixture baselines for startup, changed-file scanning, tokens, RSS and dependent invalidation | Resource targets intentionally await actual baseline; no performance PASS claimed |

## Required schema deliverables

For each schema: versioned SDN authority, compatible reader, valid/invalid golden fixtures, unknown-version and cross-repository mismatch rejection, documented migration and applicable CLI/MCP transport coverage.

| Proposed artifact | Facts that need verification |
| --- | --- |
| `phase_contracts.sdn` | Inputs, outputs, entry/exit conditions, state transitions, receipt dependencies |
| `agent_roles.sdn` | Phase/capability routing, bounded budgets, escalation, reviewer independence |
| `tool_permissions.sdn` | Role/environment/target allowlists, read/write distinction, pre-discovery authorization |
| `gate_policy.sdn` | pass/fail/waived/not-applicable semantics, not-run rejection, waiver authority/expiry/control |
| `trace_edges.sdn` | Stable UID identity, typed edges, revision pinning, checked versus inferred links |
| `knowledge_node.sdn` | Scope, routes, freshness, ownership, archive/alias identity and cache dependencies |
| `incident.sdn` | Severity/timeline, restricted dump manifest, collection loss, reproducibility/recovery evidence |
| `eval_attempt.sdn` | Frozen benchmark split, hidden-answer isolation, model/tool/context hashes and repeated metrics |

## Roadmap proof

| Milestone | Evidence needed before marking complete |
| --- | --- |
| M0 | Current skill/command/alias inventory, generated marker and checksum map, contradiction/nonportable-path findings, read-only doctor positive/negative tests |
| M1 | Schemas/readers, transition/trace implementation, immutable receipts, dependency invalidation, cross-repo mismatch fixtures, status/explain audit trail |
| M2 | Reusable canonical capabilities, deterministic adapter generation, checked imports/permissions/token size, legacy aliases and migration fixtures |
| M3 | Shared domain validation through CLI/MCP/caret/CI, capability negotiation, visible phase/gate receipts, authorized agent/task/session integration |
| M4 | Offline restricted dumps first, similarity and debugger adapters, reproducible capsules, telemetry/recovery links and incident pilot |
| M5 | Balanced authorized retrieval, semantic claim review, archival aliases, rule fixtures, frozen replay ladder and metrics |
| M6 | Feature and historical incident pilots per major subsystem, shadow-gate false-positive/time data, reviewed protected-branch enforcement and scoped opt-outs |

## Reuse and integration constraints

`src/review/contract.js` already provides closed field validation and versioned review schemas. `src/release/contract.js` supplies reusable digest and exact candidate/admission identity contracts. Integrate with these authorities rather than introducing a competing release reviewer or signing mechanism.

`scripts/build.sh` compares canonical CLI/MCP/domain files against plugin projections with `cmp`, checks managed guidance through `scripts/project-self-review-guidance.js --check`, and runs named test files. A new file alone does not enter the build gate automatically. Explicitly register applicable tests and projected modules through the existing build/distribution design.

Knowledge authorization is normative in `doc/00_llm_process/knowledge/llm_wiki_scope_resolution.md`: apply before discovery, read, export and cache lookup. A user-supplied internal path is not access authority. Preserve source disagreement, restrictive policy composition and dependency-scoped invalidation.

No tests have been run for proposed functionality. Existing source contracts are inspected evidence, not proof of their complete runtime correctness. External literature remains unverified and is not used to justify acceptance.
