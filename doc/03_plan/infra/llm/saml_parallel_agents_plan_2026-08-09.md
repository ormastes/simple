# SAML Parallel-Agent Implementation Plan (2026-08-09)

45 scoped lanes across 7 dependency waves.

## Status — 2026-08-10

A first vertical slice landed, cutting across waves rather than completing any
one of them. What exists and is verified:

| Lane area | Landed | Evidence |
|---|---|---|
| S3 frontend | `src/lib/common/saml/parser.spl` — line-oriented, tolerant, diagnostics instead of aborts | 40/40 spec |
| S0/S4 contract + resolution | `ir.spl` records; type/alias/optional/list handling | 40/40 spec |
| analysis (not in the original wave map) | `analysis.spl` — reachable schema, prompt binding, sensitive reach, evidence ladder | 40/40 spec; sabotage 34/40 |
| S8–S10 emitters | `emit.spl` — BAML, SDN manifest, Markdown manual, analysis report | 40/40 spec |
| S12 CLI | `src/app/saml/main.spl` + dispatch entry | runs via `bin/simple run`; `bin/simple saml` blocked on the seed |
| S13 LSP | `saml_analyze` MCP tool | verified over stdio JSON-RPC |
| IDE (not in the original wave map) | `src/app/ide/saml_analysis.spl` + feature-report row | IDE system spec 21/21; probe 4/4 |

Not started: runtime invocation (S14–S23), schema-aligned parsing (S24–S30),
BAML bridge execution (S19), evidence sidecars (S32), reference apps (S33–S36),
hardening (S39–S44). Nothing executes an LLM yet — the slice is static
analysis and projection only.

The analysis layer was not a lane in the original plan and turned out to be the
highest-value part; treat it as a first-class lane in any replan.
Design: `doc/05_design/infra/llm/saml_baml_integration_research_design_plan_2026-08-09.md`
Research: `doc/01_research/infra/llm/saml_research_2026-08-09.md`

## Agent model

Small, narrowly scoped lanes in parallel; **no lane self-certifies**. Every result gets independent higher-capability review: owned-file check, commit/SHA verification, test receipts, deliberate-red proof, architecture review, generated-file freshness, rework returned with concrete findings.

Exclusive roles for the whole project:

```text
Contract owner       shared IR/receipt/manifest schemas (00.contract, 30.ir)
Verification owner   acceptance policy, differential harness, red-team gates
Integration owner    final wiring and cross-lane publication (not lane internals)
Docgen owner         sole owner of the manual renderer entry point
```

## Ownership rules

1. Only the contract lane changes shared `00.contract`/`30.ir` records before freeze.
2. Emitter lanes own only their target lowerings and target tests.
3. Provider lanes implement ports; they do not alter feature contracts.
4. Parser lanes never weaken validator/mission-critical policy to make tests pass.
5. Telemetry lanes never capture raw content without redaction-owner review.
6. Docgen lanes never hand-edit generated examples.
7. Migration lanes never change source-of-truth semantics without compatibility reports.
8. Shared field changes require schema versioning, migration, all-emitter updates, goldens, verification approval.
9. Every lane ships a sabotage/revert test for its most important claim.
10. Never sync/rebase by overwriting a peer's newer generated/plan file; integrate via reviewed commits + regeneration from the final snapshot.

## Wave 0 — contract and adversarial gates (blocks all)

| Lane | Exclusive ownership | Deliverables | Required proof |
|---|---|---|---|
| **S0 Contract** | `src/lib/saml/00.contract/**`, canonical `SamlIR`, format/version registry | IDs, types, errors, source anchors, schema/value IR, projection/run/parse/eval receipts, lock/manifest schemas | golden SDN serialization; union-order preservation; schema migration fixture |
| **S1 Verification/red team** | conformance corpus, acceptance scripts, deliberate-red fixtures | BAML/SDN/schema equivalence policy, privacy gates, non-vacuity helpers, failure taxonomy | altered expected/schema/hash/union order/redaction each causes intended failure |
| **S2 Architecture policy** | SAML MDSOC contract + dependency checker spec/tests | dimensions, layers, transform rules, `__init__.saml` contract | direct feature→entity and feature→provider imports rejected; valid transform passes |

**Merge gate:** shared records, compatibility meaning, failure semantics, privacy defaults, and architecture edges frozen as v1.

## Wave 1 — frontend and semantic foundations

| Lane | Ownership | Deliverables | Deps |
|---|---|---|---|
| **S3 Frontend** | `10.frontend/**` | lexer, parser, recovery, AST, docstrings, source anchors | S0 |
| **S4 Resolver/types** | `20.semantic/resolver*`, `type_checker*` | names, modules, types, alias expansion, recursive classes, union checks | S0, S3 |
| **S5 Template semantics** | `20.semantic/template*`, template IR | static variables, context, escaping, bounds, BAML-compatible subset | S0, S3 |
| **S6 Client/test/eval semantics** | `20.semantic/client*`, `test*`, `eval*` | logical clients, retry/fallback plans, tests/checks/asserts/evaluators | S0, S3 |
| **S7 Incremental graph** | `30.ir/dependency*`, fingerprint/cache planning | declaration hashes, dependencies, invalidation, immutable snapshot publication | S0, S4 interfaces |

Gates: full reference syntax parses; stable diagnostics/anchors; all type forms canonicalize; union order survives parse→IR→SDN; invalid template symbol fails; recursive schema fixtures; retry/fallback cycle detection; architecture checker runs before projection; incremental edit invalidates only the expected subgraph.

## Wave 2 — independent projections and tooling bridge

| Lane | Ownership | Deliverables | Deps |
|---|---|---|---|
| **S8 Simple emitter** | `40.transform/saml_to_simple/**` | generated classes, ports, wrappers, errors, source maps | S0, S4, S6 |
| **S9 SDN emitter/codec** | `40.transform/saml_to_sdn/**`, trusted SDN value codec | schema/manifest/test/value output, deterministic reader/writer | S0, S4 |
| **S10 BAML emitter** | `40.transform/saml_to_baml/**` | exact `.baml`, generators/clients/tests, name lowering, compatibility receipts | S0, S4–S6 |
| **S11 BAML validator/doctor** | `80.adapter/baml_runtime/validation/**`, `90.tool/doctor/**` | CLI version/parse/generate/test adapter, diagnostic remap | S1, S10 |
| **S12 CLI/build/watch** | `90.tool/cli/**`, build hook, watcher | check/generate/verify/watch/init, atomic publication | S3–S10 interfaces |
| **S13 Native LSP bridge** | `90.tool/lsp/**` | SAML diagnostics/navigation, open-generated-BAML actions | S3–S12 interfaces |

Gates: pinned CLI accepts generated BAML; BAML test discovery works; VS Code/BAML LSP smoke test sees functions; source-map diagnostic returns to SAML; generated Simple compiles; SDN round-trips canonically; atomic publish; no absolute paths/secrets in output; second generation byte-identical.

## Wave 3 — runtime and AOP observability

| Lane | Ownership | Deliverables | Deps |
|---|---|---|---|
| **S14 Runtime orchestration** | `50.runtime/invoke/**`, state machine | call API, cancellation/deadline, attempts, parse/validate dispatch | S0, S6, S8 |
| **S15 Prompt renderer** | `50.runtime/prompt/**` | sandboxed templates, output-schema renderer, message/media model | S5, S9 |
| **S16 Client strategy** | `50.runtime/client_policy/**` | retry/fallback/round-robin plan, error classification, budgets | S6, S14 |
| **S17 Provider adapters A** | OpenAI Responses / openai-compatible | request/stream/tool mapping, safe errors, simulated-server tests | S14–S16 |
| **S18 Provider adapters B** | Anthropic / Gemini / Bedrock (sublanes) | same port + receipt contract | S14–S16 |
| **S19 BAML execution bridge** | `80.adapter/baml_runtime/invoke/**` | invoke generated BAML, typed result/error conversion | S10–S16 |
| **S20 AOP trace aspects** | `70.aspect/trace/**`, join-point tags | logical/attempt/render/parse/validate/eval spans/receipts | S0, S14 interfaces |
| **S21 Redaction/security aspects** | `70.aspect/redact/**`, privacy policy | sensitivity propagation, sink filters, retention, audit | S0, S20 |
| **S22 OTel exporter** | `80.adapter/otel/**` | pinned GenAI mapping, local collector integration | S20, S21 |
| **S23 Runtime cache** | `70.aspect/cache/**`, runtime cache ports | prompt/response/parse/eval cache keys and provenance | S14–S16, S20 |

Gates: simulated-provider end-to-end; one logical span + correct child attempts; deterministic retry/fallback ordering; cancellation never retries; metadata-only telemetry leaks nothing; sensitive nested field cannot reach a forbidden sink; AOP-disabled build has no trace probes; bridge and native providers return the same normalized envelope; streaming final result revalidated independently of partials.

## Wave 4 — schema-aligned parser

| Lane | Ownership | Deliverables | Deps |
|---|---|---|---|
| **S24 Corpus/oracle** | malformed-output corpus + expected receipts | versioned repairs, ambiguity, bounds, BAML differential expectations | S1, S19 |
| **S25 Candidate/loose syntax** | `60.parse/candidate/**`, `jsonish/**` | extraction, lexer, repair tree, partial stream parser | S0, S24 |
| **S26 Schema matcher** | `60.parse/schema_match/**` | class/list/map/enum/union candidate matching | S0, S25 |
| **S27 Coercer** | `60.parse/coerce/**` | policy-bounded conversions and events | S0, S26 |
| **S28 Validator** | `50.runtime/validate/**` | required/unknown fields, constraints, checks/asserts | S0, S4, S27 |
| **S29 Ambiguity/materialization** | ranker + generated class builder | deterministic tuple ranking, typed values, receipts | S25–S28 |
| **S30 Fuzz/performance** | fuzz harness + parser benchmarks | bounds, crash freedom, allocations, pathological inputs | S25–S29 |

Gates: every repair code has positive and deliberate-red fixtures; strict profile rejects all unapproved repairs/coercions; compatible profile matches spec; differential suite classifies every BAML divergence; no unbounded recursion/work; receipt exactly explains the selected value; native parser is drop-in via the same port; mission-critical parser rejects ambiguous winners above threshold.

## Wave 5 — generated docs, evidence, examples

| Lane | Ownership | Deliverables | Deps |
|---|---|---|---|
| **S31 Manual model/renderer** | sole owner of `90.tool/docgen/**` entry point | deterministic Markdown blocks: schemas/functions/clients/tests/compat | S0, S8–S10 |
| **S32 Evidence loader** | evidence sidecars + receipt verification | fixture/replay/live labels, hash/freshness/privacy gates | S1, S20–S22, S31 |
| **S33 Reference app 1** | resume extraction | nested schemas, aliases, repair, grounding, docs | all core |
| **S34 Reference app 2** | support classification | enum/union/literals, fallback, exact eval | all core |
| **S35 Reference app 3** | streaming plan | recursive/partial/final validation | all core |
| **S36 Reference app 4** | tool calling | capabilities, typed args, tool receipt | all core |
| **S37 BAML importer/migration** | `90.tool/import_baml/**` | one-way import, normalization diff, report | S10, S11 |
| **S38 Docs/skills** | maintained requirements/guide/skills/glossary | user guide, architecture refs, SPipe/Codex skill updates | accepted facts only |

Gates: manuals regenerate byte-identically; no-evidence output unchanged; capture labels truthful; stale/tampered receipts rejected; prompt docs contain no secret/runtime content by default; four reference apps run in bridge profile; importer round-trip has no unexplained loss for supported corpus.

## Wave 6 — production hardening

| Lane | Deliverables |
|---|---|
| **S39 Mission-critical profile** | strict defaults, warning promotion, evidence/approval gates, signed/hash-bound artifacts |
| **S40 Compatibility matrix CI** | OSes, Simple runtime profiles, BAML versions, provider adapters, editor smoke tests |
| **S41 Supply-chain/license** | notices, provenance, dependency lock, sandbox policy, artifact verification |
| **S42 Performance/startup** | daemon reuse, lazy provider/aspect load, parser arenas, PGO-ready profiles |
| **S43 Formal properties** | Lean4: state transitions, retry budgets, receipt completeness, publication atomicity, repair-budget monotonicity, sensitive-flow (10 properties, design doc §21.4) |
| **S44 Independent final audit** | no mislabeled mocks, no stale docs, no vacuous oracle, no hidden content capture, every "landed" claim re-run |

## Integration sequence

```text
S0/S1/S2 -> S3/S4/S5/S6/S7 -> S8/S9/S10 -> S11/S12/S13
         -> S14/S15/S16/S19 -> S20/S21/S22 -> S24..S30
         -> S31/S32/S33..S38 -> S39..S44
```

S17/S18 proceed once runtime ports freeze; they do not block the BAML bridge milestone.

## Per-lane review checklist

Owned paths only · no duplicate shared types · no placeholder success paths · explicit failures · public API documented · unit + integration tests run · deliberate-red proof · generated files regenerated, never hand-edited · source maps/diagnostics checked · privacy classification reviewed · allocation notes for hot paths · unsupported behavior recorded exactly · commit bytes independently inspected · every "pass" claim includes command and result receipt.

## Recommended first four slices

1. **Slice 1:** frontend + `SamlIR` + strict BAML/SDN/Markdown emitters + `check/generate/doctor --baml`; resume example accepted by pinned BAML CLI; byte-identical regeneration + deliberate-red failures.
2. **Slice 2:** native Simple wrapper + BAML execution bridge + call/error receipts + AOP tracing + metadata-only OTel + redaction + evidence-bound manuals.
3. **Slice 3:** native provider port + simulated adapter + prompt renderer + retry/fallback + streaming; BAML SAP retained for parsing; differential runtime tests.
4. **Slice 4:** native parser (corpus → candidate/loose → matcher/coercer/validator) + differential mode + mission-critical profile + fuzz/perf gates.

Acceptance gates and risk register: design doc §22–§23.
