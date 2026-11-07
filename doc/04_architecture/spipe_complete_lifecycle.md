# SPipe — Complete Engineering, Incident, Knowledge and LLM Training Lifecycle

Status: proposed architecture and migration plan (2026-10-22). This is a design proposal, **not** a claim that these commands and gates are implemented.

## 0. Baseline and governing principles

Current Spipe `main` was inspected on 2026-10-22. Relevant existing contracts include `doc/00_llm_process/skill_command/skills/pipe/impl/skill.md` (15-phase implementation), `.../verify/skill.md`, `.../verify/bug_review/skill.md`, `.../knowledge_ownership/skill.md`, `doc/00_llm_process/knowledge/llm_wiki_scope_resolution.md`, `doc/00_llm_process/spipe/{INDEX,skill,loop,review_admission,llm_finetune}.md`, and provider-specific Claude/Codex/Gemini skills. These are to be integrated, not blindly superseded. Note that the `spipe/skill.md` is specifically a **BDD test-writing** skill; a lifecycle dispatcher must have a distinct name. Repository content changes after this inspection require a fresh inventory.

Principles: single canonical phase contract; thin provider adapters; phase outputs that are immutable/versioned evidence; risk-adaptive gates; independent review and reproducible verification; no fictional tool output; explicit authority for privileged operations; low startup/token/memory overhead; and bidirectional traceability. Use SDN for registries and machine-readable policies, Markdown for human rationale, and content-addressed blobs for large dumps. Avoid a second competing process or another implementation of the same validation logic.

**Terminology:** `SPipe` today also names Simple's spec→test→report system. Use `spipe lifecycle` for workflow orchestration, `spipe spec` for BDD tooling, and `spipe knowledge` for wiki/skill management. Existing commands remain aliases until deprecated through usage evidence.

## 1. Lifecycle overview

Three linked workflows share one evidence and traceability graph:

1. **Change workflow:** requirements → research → codebase exploration → requirement hardening → risk plan → architecture/design → plan hardening → fail-first acceptance/BDD → implementation/unit/integration → independent verification → release/change management.
2. **Operational workflow:** observe/detect → triage/contain → acquire dump → analyze → reproduce → fix → regress/prevent → verify recovery → publish incident learning. P0/P1 containment may precede paperwork, but never erases evidence and must be retrospectively reconciled.
3. **Learning workflow:** root-cause retrospective → candidate skill/process/wiki update → evaluate against historic bugs → smaller-model replay → review and enforce → prune stale/duplicate guidance.

States per change: `proposed → investigating → defined → designed → test_ready → implementing → verifying → releasable → released → observing → closed`; exceptional states `blocked`, `rework`, `abandoned`, `rolled_back`. Gate results are `pass`, `fail`, `waived`, `not_applicable`; waivers require authority, reason, expiry, compensating control and evidence. Never silently treat `not_run` as pass.

## 2. Phase contracts, agents and quality gates

|Phase|Specialist agent / skill|Required artifact and exit gate|
|-|-|-|
|1. Requirement analysis|`requirements-analyst`|Problem, stakeholders, scope/non-goals, use cases, measurable initial acceptance goals, open questions; no premature solution commitment|
|2. Research|`researcher`|Internal prior art + external primary sources, alternatives, evidence dates/licenses, trade-offs, uncertainty and gaps|
|3. Codebase exploration|`repo-explorer`|Relevant ownership graph, existing APIs, call/data paths, tests, performance constraints, duplication candidates, compatibility baseline; pin commit|
|4. Requirement hardening|`requirements-reviewer`|Stable REQ/NFR IDs, ambiguity/conflict checks, edge/error/security/privacy cases, selected options, acceptance trace; owner approval for choices|
|5. Risk analysis and planning|`risk-analyst`|Failure modes, threat model, privacy/compliance impact, migration/rollback, effort/dependencies, risk rank; mitigation/test owners|
|6. Architecture and detailed design|`architect`|ADRs, interfaces/ABIs, sequencing/data/ownership, concurrency and resource budgets, alternatives, portability matrix, operability; architecture review|
|7. Plan hardening|`plan-reviewer`|Ordered tasks, independent work packages, merge boundaries, CI matrix, acceptance-gate mapping, rollback checkpoints, critical path; no unresolved blocking dependency|
|8a. Acceptance-first BDD|`acceptance-test-author`|Fail-first observable system scenarios mapped to requirements and requirements mapped back; meaningful negative tests; verified red|
|8b. TDD implementation|`implementer` + `unit-test-author`|Small red→green→refactor cycles; unit/integration/contract/property/fuzz tests where justified; compiler/test runner independent; no hidden stubs|
|9a. Independent code review|`reviewer`|Correctness, ownership/borrow, race/lifetime, compatibility, test quality, duplication and design deviation; reviewer distinct from author when risk demands|
|9b. NFR validation|`perf-reviewer`, `security-reviewer`, `compliance-reviewer`|Baseline/delta startup, CPU, memory, I/O, latency, throughput; SAST/dependency/secrets/fuzz/threat tests; privacy/data handling/license controls; platform coverage|
|9c. Release/document verification|`release-validator`, `trace-auditor`|Binary provenance, bootstrap/rebuild, package/ABI, smoke/rollback, all REQ→scenario→tests→code, updated docs, links, orphan docs and exceptions|
|10. Release and change management|`release-manager`|Approved exact revision, tagged artifacts and checksums, compatibility and migration notes, staged rollout, maintenance windows if needed, rollback and monitoring owners|
|11. Debugging and incident operations|`incident-commander`, `debugger`, `reproducer`, `recovery-verifier`|Alert/timeline, impact/severity, containment, dump manifest, root cause confidence, deterministic reproduction, bug-fix and similar-bug tests, recovery receipts|
|12. Retrospective and prevention|`rca-analyst`, `process-maintainer`|Causal chain and escape-point analysis, detection/prevention controls, doc/skill/wiki proposals, measurable follow-up, authorized promotion and enforcement tests|
|13. LLM learning/evaluation|`eval-curator`, `model-evaluator`, `knowledge-curator`|Frozen incident benchmark, wiki/skill baseline vs candidate, blinded replay, smaller-model repeated trials, quality/cost/latency regression checks; no train-on-test leakage|

Phases 1–7 may loop (design exposes a missing requirement), phase 8 may return to design, phase 9 can reject any prior phase. Phases 11–13 run continuously as necessary, not only after release. Fast paths for docs-only/low-risk changes still generate a minimal record with explicit skipped-gate reasons. Production, security, firmware and mission-critical changes must not use low-risk defaults.

## 3. Agent architecture and skill dispatch

Create a **canonical skill per capability**, rather than one long skill per model. Suggested tree:

```text
skills/
  lifecycle/                 # dispatcher and gate semantics
    SKILL.md
    references/phases.sdn
  discovery/{requirements,research,exploration}/
  definition/{requirements_hardening,risk,architecture,plan_review}/
  delivery/{bdd,tdd,implementation,review,performance,security,privacy,compliance,traceability,release}/
  operations/{monitor,triage,dump,reproduce,debug,mitigate,recovery,rca}/
  learning/{wiki_curate,skill_maintain,bug_eval,model_ladder,prune}/
  tooling/{trace32,git_jj_scv,ci,md_lsp,compiler,build_runner}/
```

Each `SKILL.md` is short: trigger, preconditions, exact inputs/outputs, authority, safety boundaries, commands, evidence schema, acceptance gate and links to deeper references. Canonical `skills/` is projected into Claude/Codex/Gemini/Kimi wrappers from one generator; **never hand-edit generated copies**. Preserve the present managed source markers and generated-file checksum checks. Feature experts and layer experts are orthogonal: a compiler parser task selects `feature:parser` and `layer:compiler`, then the phase skill. Tool specialists add TRACE32, CI or OS knowledge without replacing process policy.

**Orchestrator agent:** chooses phase, retrieves minimal context, schedules permitted specialists, verifies receipts, records decisions and requests human approval at authority boundaries. **Specialists:** narrow ownership, least-privilege tools, bounded time/context, no unilateral gate waivers or release approvals. **Independent gatekeeper:** validates evidence, not textual claims from implementers. If no separate agent is available, use a separate review pass and disclose reduced independence. Use specialized agent identity only when its skill and tools are relevant; avoid dozens of resident model processes.

Agent routing record (SDN example; proposed schema):

```sdn
agent_route {
  phase = "incident.reproduce"
  role = "reproducer"
  skills = ["operations/reproduce", "delivery/bdd"]
  tools = ["repo.read", "test.run", "dump.read_sanitized", "bug.search"]
  model_tier = "small_first"
  escalation = ["low_confidence", "repeat_failure", "high_severity"]
  max_iterations = 3
  side_effects = "workspace_only"
}
```

Model routing: deterministic static checks first; smallest proven model for classification, retrieval and bounded edits; stronger model for architecture uncertainty, severe incidents and independent arbitration. Avoid changing the required reviewer strength solely to save cost. Include token/time budgets and stop conditions.

## 4. MCP and CLI contract: one core, multiple adapters

Expose tool groups through a versioned Spipe service, with **the same domain logic** used by CLI, MCP, IDE/caret and CI. Candidate endpoints (not existing API claims):

|Group|Tools|Safety/evidence|
|-|-|-|
|Lifecycle|`process.start/status/next`, `phase.enter/submit`, `gate.evaluate/explain`, `decision.record`, `artifact.link`|Revision-pinned run, immutable gate receipts, authorized waivers|
|Research/knowledge|`knowledge.resolve/search/read/propose`, `evidence.capture`, `wiki.rebalance/diff`|Scope authorization before lookup; cite raw/doc origins; proposals only by default|
|Source/trace|`repo.symbols/impact`, `trace.query/check`, `md.links/orphans`, `change.diff`|Incremental index, scoped filesystem, changed-node invalidation|
|Test/verify|`test.select/run`, `bench.compare`, `security.scan`, `coverage.map`, `ci.receipt.verify`|Artifact hashes, environment IDs, no fake pass from missing binary|
|Operations|`incident.create/triage/timeline`, `dump.catalog/load`, `debug.attach/query`, `repro.record/run`, `recovery.verify`|Confidentiality classification, bounded dump redaction, environment permissions|
|Learning|`bug.similar`, `eval.freeze/replay/compare`, `skill.propose/lint/verify/promote`, `wiki.dedupe/prune`|Held-out evaluation, reviewer approvals, reversible promotions|
|Release|`release.plan/check/promote/rollback`|Human-authorized irreversible actions, provenance, rollout gates|

Return structured `result`, `evidence_refs`, `source_revision`, `authority_scope`, `duration_ms`, `resource_usage`, `errors` and `next_actions`. Prefer SDN on disk with a versioned JSON-RPC-compatible MCP transport if required by MCP clients. Credentials never enter prompts, wiki, dumps or cache keys. Read-only operations have distinct permissions from write, deploy, dump attachment or remote debugging. Every externally mutating tool must be allowlisted per role, environment and target; dry-run and explicit approval for production mutation. The agent loop mechanism already exists: extend its state/receipts, do not reinvent the scheduler.

## 5. Canonical traceability and artifact model

```text
REQ/NFR → risk/threat → ADR/design → acceptance scenario
     → system/integration/unit tests → implementation symbol/build
     → verification receipt → release artifact → telemetry/incident
     → root cause → prevention test → knowledge/skill revision → eval
```

Use stable UIDs, explicit typed edges (`satisfies`, `tests`, `implements`, `depends_on`, `observed_in`, `prevents`, `supersedes`), and provenance (repo, commit, path, symbol/node ID, content hash, creator, timestamp, permissions). The graph is indexed incrementally from Markdown/SDN/code/test AST rather than copy-pasted into multiple databases. **No inferred link is acceptance evidence** until checked. File move keeps UID; content change invalidates dependent checks; cross-repository edges pin versions. Existing `# @cover`, REQ IDs, Spipe spec docstrings, link validator and Simple parser/AST caches should be reused. Distinguish logical identity from XXH3 fast cache fingerprints; verify content on collisions and use BLAKE3/cryptographic provenance where untrusted changes or security need it.

Suggested per-host project outputs:

```text
.spipe/
  process/runs/<run-id>/manifest.sdn
  process/runs/<run-id>/gates.sdn
  process/runs/<run-id>/evidence.sdn
  incidents/<incident-id>/incident.sdn
  incidents/<incident-id>/dump_manifest.sdn
  evaluations/<eval-id>/manifest.sdn
  runtime/cache/                 # disposable, noncanonical
```

The project's `doc/01_research`, `02_requirements`, `03_plan`, `04_architecture`, `05_design`, `06_spec`, `07_guide`, `08_tracking`, `09_report` remain the normative document home where already established. Do not make `.spipe/process` another source of truth for those documents. CI and local receipts identify exact compiler binary, bootstrap phase, OS/ISA, flags, test selector, source revision and cache provenance.

## 6. Operational incident/debug process (deep workflow)

1. **Detect:** alerts from crash, watchdog, correctness monitor, performance/security anomaly, CI regression or user report; record first-seen time and scope. Suppress repeated noisy alerts by fingerprint without losing distinct symptoms.
2. **Triage:** severity, blast radius, reproducibility, privacy/security risk, affected versions, rollback candidate, on-call owner. Search similar incidents with exact and semantic retrieval; keep both direct matches and disconfirming evidence.
3. **Mitigate:** safe containment, feature toggle, rate limit or rollback with approved operator actions; preserve pre-mitigation evidence and announce affected data validity. Security incidents use separate access/notification policy.
4. **Acquire:** crash dump, TRACE32/JTAG target memory/registers, core dump, logs, traces, symbols, firmware image, environment and build manifest. Record offsets, timestamps, checksum, access class and collection loss. Never automatically export unrestricted memory to remote LLMs.
5. **Analyze:** timeline, faulting context, control/data-flow, invariants, suspected root causes with confidence, counterexamples. Load only relevant dump pages/symbols lazily; allow T32 CMM/DAP/GDB adapters and offline replay.
6. **Reproduce:** pin source, binary, configuration, seed, inputs, CPU/OS/ISA and timing assumptions. Introduce a failing BDD/system or lower-level test; separate deterministic reproductions from probabilistic race reproductions, recording attempt counts.
7. **Fix:** smallest safe change, tests for adjacent/similar failure modes, ownership/concurrency/invalidation checks, no unsupported workaround masquerading as root-cause repair.
8. **Recover:** validate recovery of persistent state, idempotence, replay/restart behavior, data consistency and absence of recurring alert; confirm production telemetry for a defined observation window.
9. **Close and learn:** timeline, contributing factors, why requirement/design/test/review/monitoring missed it, preventive controls with owner/deadline and measurable proof; feed phases 12–13.

Record unsuccessful hypotheses and dead ends concisely so the next agent avoids repeating them. Incident resolution and knowledge publication are separate approvals; P0 closure should not wait on optional model retraining.

## 7. Retrospective → enforceable skill/process/wiki improvements

For every material defect, ask: (a) What proximate condition failed? (b) Why was the condition possible? (c) Why did detection miss it? (d) Which earlier phase could have prevented it at lowest ongoing cost? (e) Would a rule, test, tool, wiki entry, or model adaptation have helped? (f) What is the false-positive or performance cost of enforcement?

Classify preventive actions in descending reliability:

1. **Executable guard**: compiler/linter/type system/static verification/test/CI gate with an adversarial regression fixture.
2. **Structured process gate**: required evidence or reviewed exception in the phase contract.
3. **Skill update**: concise decision procedure and tool instructions for an agent.
4. **Wiki guidance**: reusable explanations, diagnosis strategy, symptom search route and examples.
5. **Training corpus**: license/privacy-cleared examples after robust evaluation.

Do not rely on an instruction in a wiki to enforce a critical safety property. A skill/process change is accepted only after positive and negative fixtures, proof it is invoked at the relevant phase, backward compatibility or migration, token/time impact and a reviewer sign-off. Record `incident → failed-control → proposed-update → fixture → measured-result → promoted-version`. Roll back rules that create unacceptable false positives; do not delete their provenance.

## 8. Tree-structured LLM wiki and debugging strategy

Preserve existing ownership scopes (`common`, `company`, `organization`, `project`, `user`, `host`) and surfaces (`raw`, `wiki`, `doc`, `skills`, `runtime`), access policy, `index.md` at every navigable directory and bounded context resolution. **Tree is for primary navigation; cross-links form a DAG** so topics do not need duplicated text.

```text
wiki/
  index.md
  engineering/index.md
  engineering/process/index.md
  engineering/compiler/index.md
  debugging/index.md
  debugging/symptoms/{crash,hang,corruption,perf,build}/index.md
  debugging/strategies/{bisect,dump,replay,concurrency,cache}/index.md
  debugging/platforms/{linux,windows,macos,bsd,simpleos}/index.md
  debugging/hardware/{riscv,nvme,jtag,gpu}/index.md
  lessons/index.md
```

Each index contains a 1–3 sentence scope, bounded child routes, when-to-read triggers, strongest canonical links and freshness metadata. Leaves have: `symptom`, `applicability`, `quick_checks`, `diagnostic_strategy`, `counterexamples`, `evidence`, `prevention`, `related`, `last_verified`, `owner`. Keep incident-specific logs in raw/incident records and link from concise reusable lessons. No private path/data in public common-scope wiki.

**Balancing and pruning algorithm:** collect retrieval/usage counters by node, token size, branch fanout, overlapping claims, stale revision and traversal failure. Split overloaded nodes by stable domain or diagnostic discriminant; merge sparse nodes only if ownership and meaning align; alias moved UIDs; keep short summaries at ancestors. Use configurable soft targets initially (for example 5–12 children and 300–900 tokens/index), *not* arbitrary hard limits. Dedupe via normalized claims + links + human semantic review, not hash similarity alone. Mark `active`, `needs_review`, `superseded`, `archived`; archive, don't silently delete historical instructions, before migration/retention approval. Deleted ineffective guidance requires evidence from evaluation and replacement links. Descendant changes invalidate only dependent summaries and cached prompts, consistent with the current wiki scope contract.

## 9. LLM training and model-ladder evaluation

This is primarily **retrieval/skill/process optimization**, with weight fine-tuning only when needed. Extend existing `spipe/llm_finetune.md` attempt records rather than creating a disconnected trainer.

1. Build a de-identified bug benchmark: observable symptom, repository revision, reproducible environment, permitted logs/dump excerpts, expected cause, minimal fix, prevention test and scoring rubric.
2. Split by *root-cause family and time/repo*, not random snippets: train/dev/held-out. Keep hidden answers and future incidents out of the agent's retrieval corpus during evaluation.
3. Run baseline agent with current skills/wiki, fixed tools, prompt budget, model/version/seed where controllable. Capture success, correct cause, passing tests, regressions, number of tool calls, time, peak memory, token cost and unsafe action attempts.
4. On failure, identify whether the missing factor was **tool access, raw evidence, search routing, domain knowledge, decision strategy, process gate or model reasoning**. Patch the narrowest layer, then rerun all relevant past incidents and adversarial negatives.
5. On success, repeat with one or more **smaller models** under matched tools and context. Use repeated trials for nondeterminism, report confidence intervals, compare solve@1, solve@k and budget; use escalation-to-large routing where small model fails.
6. Promotion requires no critical safety regression, statistically and practically useful success gain, acceptable latency/cost, owner authorization and privacy/license review. Freeze evaluation artifacts and version wiki/skill hashes.
7. Optionally fine-tune/LoRA only on properly licensed, separate training data if the skill/wiki strategy plateaus. Keep a clean held-out set; retest after changing model, quantization or context window.

**Do not overfit:** repeated evaluation on the same held-out set leaks information; periodically freeze a new prospective cohort. Do not claim smaller-model equivalence from one successful replay. Measure model-agnostic deterministic controls separately.

## 10. CI enforcement and runtime efficiency

* **Pre-commit:** changed-file syntax, SDN/schema, link/UID integrity, stub scan, tiny targeted tests; aim for seconds, never whole-repo scan.
* **PR:** requirement/scenario/impl mapping, red-first provenance where supported, changed impact tests, code review, security/secrets and duplication, NFR deltas, exact revision receipts.
* **Main/release:** full platform matrix, cross-compilation and native smoke, bootstrap phase verification, artifact provenance, performance trends, ABI/compatibility, rollback drill as applicable.
* **Periodic:** wiki stale/dedupe/orphan scan, incident action aging, retrospective gate coverage, model-ladder evaluation, policy/schema compatibility and dependency security.
* **Production:** anomaly monitor, release canary and rollback triggers, incident evidence collection with retention/access boundaries.

Share build/test/read-only immutable caches through the build runner, keyed by source/compiler/flags/ISA/env and authorization. Prefer incrementally indexed AST/metadata and deterministic static tools over agent tokens. Selectively load skills and wiki branches; retrieve only the relevant symbols and dump pages. Support no network/air-gapped firmware work and manual invocation for every phase and CI worker. CI does not authorize production access automatically. Cache failures must never create false verification passes.

## 11. Migration and implementation roadmap

**M0 — inventory and canonicalization:** index existing provider skills and generated markers; map old `/research`, `/design`, `/impl`, `/verify`, `/release`, `/bug_review`, `/spipe_loop`, `/agents` into phase IDs. Detect contradictions (for example `spipe/skill.md` mistakenly says 'formerly SPipe') and stale hardcoded host paths. Keep compatibility aliases.

**M1 — schema + trace core:** implement process/phase/gate/evidence/waiver SDN schemas and CLI; stable IDs, links, receipts, invalidation; tests for cross-repo policy/schema mismatches. Make status/explain/manual overrides audit-ready.

**M2 — phase skills + adapter generation:** split 15-phase implementation into reusable requirement, research, explore, risk, architecture, plan, BDD/TDD, review and release skills. Provider adapters generated from one source. Validate imports, permissions and prompt-size budgets.

**M3 — MCP and caret:** expose the shared CLI/service through MCP; agent role registry, capability negotiation, user approvals, visible phase/gate status; integrate task/agent/session and manual worker access. No live remote operation without authorization.

**M4 — incident pipeline:** bug similarity, dump manifests, TRACE32/DAP/GDB adapters, reproducible test capsules, monitoring integration, recovery receipts and incident-to-prevention links. Begin with offline/local read-only dump tools.

**M5 — knowledge curation and training:** balanced index routing, claim dedupe, archival aliases, rule regression fixtures, frozen bug benchmarks, small-model ladder and metrics dashboard.

**M6 — graduated enforcement:** pilot on one feature and one real historical bug per major subsystem; shadow gates before blocking; track false positives and wall time; then require applicable gates on protected branches. Keep opt-out only through recorded, scoped authority.

## 12. Acceptance criteria for SPipe lifecycle itself

1. A new feature can be followed from initial request to release artifact and back to exact tests/requirements without broken, guessed or orphan links.
2. A hardening change that lacks a negative acceptance test cannot claim `test_ready`; deliberate waiver is visible and authorized.
3. A stale or missing tool/compile binary produces `not_run/fail`, not a pass; receipts pin executable and revision.
4. A P1 crash yields a redactable dump manifest, root-cause hypothesis, reproducible test, preventive test, recovery evidence and reviewed lesson.
5. A false/duplicated wiki strategy can be identified, evaluated, archived with redirects and excluded from default retrieval without losing provenance.
6. Each new process/skill rule is tested on a counterexample and known passing example; the review proves it actually triggers.
7. A frozen bug corpus runs current vs proposed wiki/skill and large vs smaller model with exact cost, latency, safety and solve metrics; no hidden answers exposed during replay.
8. Unauthorized knowledge scope or dump access fails *before* discovery/read/cache retrieval, including when the requester names an internal path.
9. Same canonical phase gives equivalent validation across Claude, Codex, Gemini and CLI; adapters do not diverge.
10. Incremental workflow stays fast: measured changed-file scan, context-token count, process startup, peak memory and cache invalidation; set numeric budgets from actual baseline rather than invented thresholds.

## 13. Immediate next engineering tasks

1. Produce `phase_contracts.sdn`, `agent_roles.sdn`, `tool_permissions.sdn`, `gate_policy.sdn`, `trace_edges.sdn`, `knowledge_node.sdn`, `incident.sdn`, `eval_attempt.sdn` schemas with compatible versioned readers.
2. Build a read-only `spipe lifecycle doctor` that lists current skills/commands, collisions, generated duplicates, broken links, nonportable absolute paths and stale terminology.
3. Add golden tests from the existing 15-phase skill, verify skill, review-admission policy, cross-repo self-review schema bug and wiki authorization semantics.
4. Implement the shared lifecycle state machine and gate receipts, then agent/MCP dispatch; integrate before rewriting all skills.
5. Pilot full feature workflow and one historic incident; compare token/time/memory cost and regression coverage to the current process.

## References and source anchors

* Current Spipe repository: https://github.com/ormastes/Spipe
* Canonical skills and loop: `doc/00_llm_process/skill_command/skills/pipe/`, `doc/00_llm_process/spipe/`
* Knowledge authority: `doc/00_llm_process/knowledge/llm_wiki_scope_resolution.md`
* Existing LLM fine-tune loop: `doc/00_llm_process/spipe/llm_finetune.md`
* Existing cross-repo policy schema mismatch: `doc/00_llm_process/spipe/self_review_policy_cross_repo_bug.md`
* Agent skill empirical studies: https://arxiv.org/abs/2608.08453 and https://arxiv.org/abs/2610.11169 (use to inform evaluation, not as proof of this proposed implementation).
