# SPipe Bug Management, Debug Knowledge, and Evidence Orchestration

**Research, architecture, policy, data design, skill update, and parallel implementation plan**

- **Date:** 2026-09-03
- **Status:** Proposed implementation baseline
- **Primary repositories inspected:**
  - `ormastes/simple` at `bd5d012db308f22b2726da889fc7901ca362dffb`
  - `ormastes/Spipe` at `ac06e63d263ff474c5204f31d3e59a1a4fe767fb`
- **Scope:** normal software, compiler/runtime, host applications, embedded firmware, hardware-assisted debugging, remote/field reproduction, and statistical defect analysis
- **Deliverables represented by this document:** policy, canonical data model, retrieval architecture, symptom playbooks, evidence capture contract, firmware-variant rules, intake automation, common/project knowledge layering, CLI/MCP design, skill hierarchy, tests, migration, and parallel-agent schedule

---

## 1. Executive decision

SPipe should not treat a bug as one mutable Markdown page plus an issue link. It should treat a bug as a **versioned case with an append-only evidence ledger**, backed by a **reusable symptom-to-check knowledge base**, an **immutable artifact vault**, and **derived LLM wiki/search views**.

The target system has four planes:

1. **Case plane — project facts**
   - One canonical textual database for bug identity, state, observations, environments, hypotheses, experiments, evidence, cause, fix, and verification.
   - Facts are project-scoped and can include confidential data.
   - Evidence and hypothesis outcomes are append-only. Corrections supersede prior rows rather than rewriting history.

2. **Knowledge plane — reusable debugging knowledge**
   - Common SPipe knowledge describes symptom classes, discriminating checks, capture recipes, safe assertions/logging, reproduction tactics, statistical methods, and tool recipes.
   - Project-local overlays specialize common knowledge for a product, component, SoC, firmware, lab, or organization.
   - Local knowledge can be promoted to common only through an explicit reviewed workflow with provenance and redaction.

3. **Evidence plane — raw and derived artifacts**
   - Dumps, ELF/PDB/DWARF, traces, logs, register snapshots, firmware images, NAND distributions, and test datasets live outside the textual DB in an immutable content-addressed store.
   - The textual DB stores hashes, sizes, types, provenance, parser receipts, security classification, and relationships.
   - Untrusted artifacts are never executed automatically.

4. **Retrieval plane — generated views**
   - Exact identifiers and fingerprints first.
   - Fielded lexical retrieval next.
   - Structural similarity and graph relations next.
   - Optional semantic embeddings only as a supplemental recall lane.
   - Rank fusion produces a deterministic, explainable result.
   - Markdown LLM wiki pages, dashboards, and “what to check next” views are generated; they are not canonical write targets.

### Required behavioral change

Before an LLM proposes a root cause, it must:

1. normalize the new observation;
2. look up exact and similar prior cases;
3. retrieve both successful fixes and **refuted hypotheses**;
4. state which prior evidence applies and which does not;
5. choose the next check for information gain;
6. record the result immediately;
7. only then update the hypothesis set.

This directly prevents the repeated investigation failure visible in the current `E-MIR-TYPE-ZeroKind` case, where five plausible hypotheses were independently pursued and refuted before direct measurement corrected the model of the failure.

---

## 2. Goals and non-goals

### 2.1 Goals

The update must make these operations routine and cheap:

- Find prior bugs with the same error code, normalized stack, event sequence, hardware context, timing pattern, distribution shape, or root-cause family.
- Convert a vague symptom into an ordered checking strategy.
- Explicitly represent “we do not yet know what to check” and select the next observation by expected information gain.
- Generate a bounded verification scenario or diagnostic firmware plan from a symptom and hypothesis.
- Decide whether to reproduce locally, in simulation, on HIL, or in the real environment.
- Decide whether one runtime-configurable image is adequate or several firmware variants are necessary.
- Automatically ingest bug notifications and artifact references without losing messages, misbinding symbols, or executing untrusted content.
- Preserve exact commit, dirty state, build ID, toolchain, configuration, target, and hardware identity for every evidence item.
- Move reusable knowledge from a project into SPipe common knowledge without copying or weakening safety rules.
- Support deterministic operation without embeddings or online services.
- Add statistics only where repeated/noisy/distributional evidence warrants it.

### 2.2 Non-goals

This design does not:

- replace GitHub Issues, Jira, email, or a company ticket system;
- put large binary artifacts into Git;
- let an LLM flash firmware or write hardware without existing authorization and safety gates;
- infer a cause from textual similarity alone;
- claim a bug is reproduced merely because a log resembles a prior log;
- make the generated wiki authoritative;
- require embeddings for baseline operation;
- allow a project overlay to silently weaken common security, privacy, or hardware safety policy.

---

## 3. Current-state audit

## 3.1 Simple bug database

The current Simple bug model is useful as a small offline registry, but it is too thin for debugging knowledge.

### Present

- `src/lib/nogc_sync_mut/database/bug.spl`
  - basic bug identity, severity, status, title, description, file/line, reproduction text, fix strategy, investigation log, dates, and validity;
  - active and archived tables;
  - textual SDN persistence.

- `src/app/bug_add/main.spl`
  - adds a basic record from command-line fields.

- `src/app/bug_gen/main.spl`
  - generates recent/open/closed Markdown summaries.

- `src/lib/nogc_async_mut/mcp/bugdb_resource.spl`
  - exposes read/add/update resources through MCP.

- `doc/08_tracking/bug/bug_db.sdn`
  - contains active bugs and a large accumulated `bug_descriptions` table.

### Problems

1. **The case model is not rich enough.**
   - There is no structured symptom, fingerprint, environment, source identity, artifact, hypothesis, experiment, scenario, evidence, duplicate relation, root cause, verification claim, or release linkage.

2. **The MCP implementation has a second parser.**
   - It manually parses table text instead of reusing the canonical database API.
   - This creates schema drift and makes fail-open behavior more likely.

3. **Field parity is incomplete.**
   - Rich investigation fields in the database/document workflow are not consistently returned or updated through MCP.

4. **Rich cases live as fragmented prose.**
   - The most useful debugging knowledge is in individual Markdown documents rather than normalized case/evidence records.
   - Related case documents are discoverable only by filename/text search and human context.

5. **The SDN integrity boundary is awkward for direct editing.**
   - The current file includes CRC headers and is intended to be written through tooling.
   - A policy that tells LLMs to edit the SDN directly would be unsafe; all mutations should go through one transactional service.

6. **No similar-bug API exists.**
   - Current resources can list or get records, but do not provide exact fingerprint lookup, fielded search, related cases, negative precedents, or search explanations.

### Required change

Create `BugCaseStoreV2` as the sole canonical writer. Existing V1 APIs become compatibility façades. MCP, CLI, generated Markdown, issue synchronization, and the LLM wiki all consume the same typed store and never parse the SDN independently.

## 3.2 Current debugging skills

Spipe and Simple already contain debug agents, a shared debug skill, bug review, T32 support, and a daily-debug loop. These should be refactored, not replaced.

### Present strengths

- Debug commands for logging, AST/HIR/MIR dumps, diagnostics, MCP/DAP, stack traces, breakpoints, T32 trace/coverage/flash/reset, and common bootstrap workflows.
- A concise reproduce → isolate → identify → fix → verify loop.
- A `bug_review` flow for external issue systems.
- A daily-debug intake path.
- SPipe’s portable host-mount and subproject-expert layout.

### Missing policy

- mandatory prior-case retrieval;
- symptom ontology and discriminating-check playbooks;
- append-only hypothesis and negative-evidence discipline;
- evidence bundle manifests;
- build/symbol compatibility gates;
- capture budgets for constrained targets;
- diagnostic firmware variant planning;
- remote real-environment data requests;
- statistical-analysis trigger rules;
- common/local knowledge references and promotion;
- parser/tool receipts;
- search-quality evaluation.

### Required skill hierarchy

The common debug policy must be canonical. Tool and target skills must extend it:

```text
debug-common
├── debug-software
│   ├── compiler-debug
│   ├── service-debug
│   └── crash-debug
├── debug-firmware
│   ├── t32
│   ├── openocd
│   ├── gdb-remote
│   ├── zephyr-coredump
│   └── esp-coredump
└── debug-statistics
    ├── intermittent-rate
    ├── performance-regression
    └── storage-cell-distribution
```

T32, OpenOCD, GDB, and platform-specific scripts are executors. They do not own the bug lifecycle or evidence semantics.

## 3.3 Current daily-debug intake

The existing `spipe_loop --daily-debug` and Simple `cmd_daily_debug.spl` form a useful seed, but they are not yet a reliable evidence-ingestion system.

### Current behavior

- read a watermark;
- fetch Outlook messages;
- extract Jira-like keys and HTTP URLs;
- classify URLs by filename suffix;
- produce a daily Markdown digest;
- save a watermark;
- optionally notify.

### Gaps to fix

- Classification by URL suffix is not sufficient for artifact trust or type.
- The driver uses message previews rather than guaranteed full bodies/attachments.
- The fetch is bounded to a small page without a complete pagination contract.
- Missing credentials or a fetch failure can produce an empty result; a watermark must never advance after an incomplete read.
- The “ISO” helpers currently use Unix-second strings and the digest filename uses an epoch-day placeholder.
- The digest does not admit artifacts into an immutable evidence bundle.
- There is no source-event idempotency key, durable inbox, retry/reconciliation state, artifact hash, parser receipt, symbol lookup, or build compatibility gate.
- There is no webhook path; once-daily polling increases latency and can miss edge cases unless reconciliation is rigorous.

### Required change

Use **webhook/change-notification first**, plus a periodic delta/poll reconciliation job. A notification only creates an immutable intake event. The cursor advances only after each event is durably admitted or explicitly quarantined with a retry state.

## 3.4 Existing search infrastructure

Simple already has reusable search contracts:

- fielded documents and facets;
- fixed-point scoring;
- BM25-oriented capabilities;
- immutable snapshots and incremental index operations;
- scope digests and visibility partitions;
- search explanations;
- top-k result types.

This is the right substrate for bug and wiki retrieval. It must not be bypassed by a separate ad-hoc bug search engine.

However, current open search-correctness bugs mean the bug-retrieval rollout must be guarded by a historical regression corpus. The first production release should support exact lookup plus a conservative lexical baseline, and enable wider BM25/fusion only after correctness fixtures pass.

## 3.5 Current rich case proves the needed schema

The current ZeroKind investigation contains information that the V1 bug schema cannot represent well:

- the original misleading diagnostic;
- direct measured fields;
- invalid-object interpretation;
- five refuted hypotheses;
- negative probe results;
- nondeterministic occurrence count across byte-identical runs;
- a costly reproduction envelope;
- the next highest-value investigation;
- a distinction between a real sibling defect and the still-open causal defect.

V2 must make all of these first-class. In particular, **negative evidence is not a comment**. It is a durable result that should suppress repeated low-value work.

---

## 4. Research-derived design principles

## 4.1 Normal software debugging

Modern crash systems separate capture from analysis because the crashing process may have corrupt state. They preserve a bounded snapshot, identifiers for loaded binaries, thread/register/stack state, and application metadata; symbols are resolved later on a better-provisioned host.

Applied to SPipe:

- keep the fatal path bounded and allocation-free;
- capture raw state with minimal interpretation;
- symbolize and parse off-target;
- bind evidence to exact executable/library identifiers;
- preserve both compact automatic dumps and on-demand diagnostic snapshots;
- store per-case metadata and privacy classification.

Compiler and service bugs additionally benefit from:

- deterministic reduced reproducers;
- automated good/bad commit bisection;
- coverage-guided fuzzing of narrow deterministic targets;
- sanitizer builds;
- delta debugging for inputs and feature/config sets;
- failed-only retries followed by affected closure and one clean full closure.

## 4.2 Embedded debugging

Embedded systems need tiered capture because RAM, flash, bandwidth, timing, and power are constrained.

Common patterns are:

- minimal crash dump: fault registers, current task/thread, exception stack;
- broader thread dump when memory permits;
- optional selected memory regions rather than unconditional full RAM;
- circular event buffers;
- compile-time and runtime filtering;
- rate-limited or first-occurrence logging;
- host-side decoding using the exact ELF/event dictionary;
- flash or host transport backends;
- persistent crash slots with integrity checks;
- hardware trace only for targeted lab escalation.

Applied to SPipe:

- every capture recipe declares its cost;
- a diagnostic build has a distinct build ID;
- no string formatting, dynamic allocation, unbounded loops, or unsafe peripheral access in a fatal handler;
- the target records compact typed event IDs and the host owns expensive formatting;
- capture loss and truncation counters are evidence.

## 4.3 Intake and issue reporting

Structured issue forms can require observed behavior, expected behavior, version, environment, reproduction, and uploads. Webhooks/change notifications reduce latency and polling load, but delivery can be retried or duplicated, so source delivery IDs and reconciliation remain necessary.

Applied to SPipe:

- GitHub/Jira/email are intake adapters, not the canonical case store;
- intake is idempotent;
- event receipts are immutable;
- attachment URLs are references until metadata and policy checks pass;
- polling remains as reconciliation, not the sole trigger.

## 4.4 Retrieval

Similar-bug retrieval is best treated as a multi-signal problem:

- exact identifiers are high precision;
- fielded lexical retrieval is transparent and cheap;
- structural fingerprints capture stack/event/config similarity;
- graph relations expose sibling causes and previous exclusions;
- semantic embeddings recover textually dissimilar descriptions;
- reciprocal rank fusion combines independent rankings without assuming comparable raw scores.

Applied to SPipe:

- lexical search remains the required offline baseline;
- semantic search is optional;
- every result explains which fields/fingerprints matched;
- similarity never automatically marks a duplicate;
- a human/agent records the relation type after comparison.

## 4.5 Statistical debugging

Statistics are useful when observations vary across repetitions, devices, time, wear, temperature, workloads, or populations. They are unnecessary for a deterministic one-shot failure with a direct causal oracle.

Applied to SPipe:

- statistics must have a declared question and sampling unit;
- raw populations are stratified before fitting mixtures;
- missingness and capture bias are checked first;
- effect size and uncertainty accompany p-values;
- drift uses time-aware tools such as control charts/EWMA;
- multimodality is not automatically interpreted as multiple causes;
- confirmatory experiments are separated from exploratory analysis.

---

## 5. Target architecture

```text
GitHub / Jira / Outlook / CI / device / lab / user
                      |
                      v
          Intake adapters + durable inbox
      (delivery id, cursor, signature, raw hash)
                      |
                      v
           Case normalizer / redaction gate
             |                         |
             v                         v
      BugCaseStoreV2             EvidenceVault
  structured textual SDN       immutable raw objects
  append-only evidence          hashes + manifests
             |                         |
             +------------+------------+
                          |
                          v
                Projection compiler
        exact index / BM25 / fingerprints /
         graph / optional semantic index
                          |
             +------------+-------------+
             |                          |
             v                          v
       LLM/debug planner          Generated wiki/views
  symptom -> check -> scenario    local + common links
             |
             v
   execution adapters / scripts / HIL / real env
             |
             v
     parser receipts + observations + claims
             |
             v
      cause/fix/verification/promotion workflow
```

## 5.1 Authority boundaries

| Authority | Owns | Must not own |
|---|---|---|
| `BugCaseStoreV2` | case state, structured facts, links, hypotheses, experiments, claims | raw binary bytes |
| `EvidenceVault` | immutable raw artifacts and derived files with hashes | bug status or conclusions |
| `DebugKnowledgeRegistry` | reviewed common playbooks and ontology | project-confidential case facts |
| Project overlay | product-specific playbooks and aliases | silent weakening of common safety |
| Projection compiler | indexes, generated wiki, dashboards | canonical edits |
| Intake adapter | source receipt and source payload retrieval | root-cause decisions |
| Execution adapter | run/flash/capture under authorization | lifecycle policy |
| LLM | plans, proposes, summarizes, invokes authorized tools | direct SDN mutation, evidence fabrication, unsupported PASS claims |

## 5.2 Canonical identifiers

Use stable opaque identifiers rather than paths as identity:

- `bug_uid`: `bug:<project_uid>:<uuid>`
- `observation_uid`: `obs:<uuid>`
- `evidence_uid`: `ev:<sha256-prefix-or-uuid>`
- `hypothesis_uid`: `hyp:<uuid>`
- `experiment_uid`: `exp:<uuid>`
- `scenario_uid`: `scn:<uuid>`
- `knowledge_uid`: `dbgk:<namespace>:<name>:<major>`
- `build_uid`: `build:<project>:<build-id-or-content-id>`
- `source_event_uid`: provider namespace + immutable delivery/message/event id

Paths, filenames, issue numbers, and human-readable aliases are attributes, not identity.

---

## 6. Bug textual database V2

## 6.1 Design rules

1. One canonical typed store and serializer.
2. Append-only evidence, hypotheses, experiments, and events.
3. Case summary fields may be updated transactionally.
4. Every mutation has actor, timestamp, source, previous revision, new revision, and content digest.
5. A malformed row, integrity mismatch, or unknown mandatory enum fails closed.
6. Large raw content is referenced by digest.
7. Markdown is generated.
8. Confidentiality and visibility are enforced before projection/indexing.
9. External issue state is synchronized explicitly and recorded; it does not overwrite stronger local evidence.
10. V1 remains readable during migration but becomes write-disabled after cutover.

## 6.2 Core tables

### `bug_cases`

One row per case:

- `bug_uid`
- `project_uid`
- `local_key`
- `title`
- `status`
- `severity`
- `priority`
- `component_uid`
- `layer_uid`
- `owner`
- `security_class`
- `created_at`
- `updated_at`
- `first_seen_at`
- `last_seen_at`
- `current_summary`
- `current_cause_state`
- `current_fix_state`
- `current_verification_state`
- `canonical_revision`
- `valid`

### `bug_external_refs`

- provider (`github`, `jira`, `email`, `ci`, `customer`, `lab`)
- external id and URL/resource id
- synchronization cursor and timestamps
- direction (`source`, `mirror`, `notification`)
- source authority and conflict policy

### `bug_observations`

One immutable report of what occurred:

- observed result
- expected result/invariant
- symptom class/subclass
- error/assert/fault code
- occurrence time and clock basis
- run id, boot id, device id pseudonym
- frequency numerator/denominator
- earliest known good / first known bad
- confidence and provenance

### `bug_environments`

Reusable normalized environment snapshots:

- source commit and dirty-tree digest
- build ID, product/FW version, symbol set id
- toolchain and dependency lock digests
- build configuration and feature-set digests
- OS/kernel/rootfs/container
- architecture/ABI
- board/SoC/revision
- boot ROM/bootloader/FPGA/firmware versions
- attached device identities where policy allows
- workload, seed, power, temperature, clock, voltage, topology
- environment capture completeness

### `bug_symptoms`

Normalized searchable symptoms:

- symptom class/subclass
- normalized message
- exact error tokens
- state transition/event sequence
- timing signature
- resource signature
- storage/ECC signature
- distribution signature
- normalization version

### `bug_fingerprints`

Multiple fingerprint kinds:

- exact error/assert id
- normalized stack signature
- top-frame/module signature
- event n-gram/minhash
- register/fault signature
- config/build signature
- I/O/protocol transcript signature
- distribution-shape signature
- source-line/call-site signature
- fingerprint algorithm/version/value

### `bug_artifacts`

Metadata only:

- evidence id
- role (`core`, `minidump`, `elf`, `pdb`, `log`, `trace`, `fw`, `config`, `dataset`, `image`)
- content hash, byte size, MIME/magic type
- source URI/object version
- capture time
- producer build/environment
- parser status and receipt
- redaction status
- encryption/classification
- retention policy
- immutable vault locator

### `bug_hypotheses`

- claim text
- predicted observations
- scope
- prior rationale
- state (`proposed`, `testing`, `supported`, `refuted`, `superseded`, `confirmed`)
- confidence
- proposer
- created/superseded timestamps
- links to supporting and refuting evidence
- “do not repeat unless” condition

### `bug_experiments`

- hypothesis
- scenario
- independent variable/change
- controlled variables
- baseline and variant build ids
- run count/seeds/order
- expected discriminating outcomes
- actual observations
- verdict
- perturbation/budget
- safety/rollback
- executor and receipts

### `bug_scenarios`

- reproduction level
- preconditions
- stimulus
- fault injection
- oracle
- required capture
- timeout
- repetitions/seeds
- cleanup
- safety
- target adapters/scripts
- result status

### `bug_links`

Typed graph edges:

- `duplicate_of`
- `same_root_cause_as`
- `same_symptom_different_cause`
- `caused_by`
- `blocks`
- `regression_of`
- `fixed_by`
- `verified_by`
- `related_component`
- `refutes`
- `supersedes`
- `knowledge_derived_from`

A similarity score is not a relation. A relation requires an explicit reviewed edge.

### `bug_verification_claims`

- claim (`reproduced`, `cause_confirmed`, `fix_effective`, `no_regression`, `field_resolved`)
- exact scenario and environment
- oracle
- runs/passes/failures
- evidence links
- scope and exclusions
- verdict (`PASS`, `FAIL`, `BLOCKED`, `INCONCLUSIVE`)
- signer/reviewer
- timestamp and expiry where relevant

### `bug_events`

Append-only case audit:

- created
- intake admitted
- state changed
- evidence attached
- hypothesis proposed/tested/refuted
- scenario executed
- fix linked
- verification claimed
- external sync
- knowledge promoted

### `bug_statistics_specs`

Only when statistics are justified:

- question
- response variable
- sampling unit and population
- strata/covariates
- planned repetitions
- randomization/blocking
- missing-data policy
- exploratory/confirmatory flag
- analysis methods
- stopping rule
- multiple-comparison policy
- output artifacts

## 6.3 Lifecycle

Use independent workflow and evidence states.

### Case workflow

```text
intake
  -> normalized
  -> triaged
  -> reproducing
  -> investigating
  -> cause_confirmed
  -> fix_candidate
  -> verifying
  -> resolved
  -> closed
```

Side outcomes:

```text
duplicate | cannot_reproduce | blocked | external_dependency |
accepted_risk | invalid | security_restricted
```

### Evidence completeness

```text
none
-> report_only
-> identity_bound
-> minimally_diagnostic
-> reproducible
-> cause_discriminating
-> fix_verifying
-> closure_complete
```

This separation prevents “status: investigating” from hiding that the only available data is a vague report, and prevents “fixed” from implying a full system or field verification that did not occur.

## 6.4 Negative evidence rules

Negative evidence must include:

- exact check;
- exact environment/build;
- expected signal;
- observed absence;
- proof that the observation channel was active and not truncated;
- scope of the exclusion;
- rerun condition.

Example:

> “Probe produced zero matching records” is not evidence unless the run reached the instrumented path, the output channel was not empty/truncated, the probe build ID matches the symbols, and a positive control proved the probe could emit.

This rule directly addresses vacuous zero-count conclusions.

## 6.5 Migration from V1 and Markdown

1. Freeze the V1 writer.
2. Parse V1 through the canonical existing library, never through a new text splitter.
3. Create stable V2 UIDs and preserve V1 ids as aliases.
4. Import each standalone bug Markdown page as:
   - one case or a linked case update;
   - one source document artifact;
   - extracted observations/hypotheses/experiments when confidence is high;
   - unparsed text retained as a note artifact when extraction is uncertain.
5. Import status and severity conservatively; conflicts become migration findings.
6. Preserve source path, Git blob hash, commit, and line provenance.
7. Detect likely related pages but do not auto-merge them.
8. Generate a migration report:
   - fully normalized;
   - partially normalized;
   - conflicting;
   - orphan description;
   - missing case;
   - duplicate alias;
   - malformed/integrity failure.
9. Verify round-trip determinism and idempotency.
10. Cut MCP/CLI/generator readers to V2.
11. Make V1 read-only for one release, then archive it.

---

## 7. Similar-bug lookup

## 7.1 Query packet

Every lookup begins with a normalized `BugQueryV1`:

- project and visibility scope;
- observed/expected behavior;
- symptom class;
- exact error/assert/fault tokens;
- normalized stack/event/protocol fingerprints;
- component/layer;
- build/source/environment facets;
- timing/frequency;
- attached evidence ids;
- exclusions;
- result limit;
- requested explanation level.

An LLM should not send a raw paragraph as the only query when structured evidence exists.

## 7.2 Normalization

### Text

- lowercase only for search copies, preserving original evidence;
- normalize whitespace and volatile addresses;
- retain error codes, assert ids, enum variants, register names, protocol opcodes, function/module names, and numeric units as high-weight tokens;
- separate “observed” from “expected” text;
- do not erase negation.

### Stacks

Create both:

- exact module/build/frame sequence;
- normalized module + function + relative offset bucket, stripping ASLR addresses.

Record stack truncation and symbol confidence.

### Events and logs

- preserve event IDs and typed fields;
- derive bounded event n-grams;
- normalize timestamps to deltas while retaining original clocks;
- include drop counts and reset boundaries.

### Firmware/hardware

- preserve architecture, SoC/board/revision, bootloader, FW build, feature digest, clock/power mode, and relevant peripheral topology;
- never merge two hardware contexts merely because the error text matches.

### Statistics/distributions

- preserve raw dataset digest;
- derive robust quantiles, center/spread/tail, overlap and modality features;
- stratify by physical hierarchy before forming a fingerprint.

## 7.3 Retrieval stages

### Stage 0 — exact lookup

Highest precision:

- bug id/external id;
- error/assert/fault code;
- build ID;
- exact artifact hash;
- exact normalized stack;
- exact event fingerprint;
- explicit graph links.

### Stage 1 — fielded lexical retrieval

Use weighted fields such as:

| Field | Suggested relative weight |
|---|---:|
| exact identifiers/error codes | 8 |
| normalized stack/event signature | 7 |
| title/current summary | 5 |
| symptom/observed/expected | 5 |
| component/layer/classification | 3 |
| root cause/fix | 3 |
| refuted hypothesis text | 3 |
| general notes/body | 1 |

Weights are a starting point and must be calibrated on the historical corpus.

### Stage 2 — structural similarity

Independent rankers:

- stack edit/Jaccard similarity;
- event-sequence similarity;
- configuration delta similarity;
- environment compatibility;
- temporal/frequency signature;
- distribution-shape distance;
- source ownership/call-graph neighborhood.

### Stage 3 — case graph

Boost linked cases:

- same cause;
- same symptom/different cause;
- previous regression;
- shared component;
- refuted precedent;
- fix family;
- matching knowledge playbook.

### Stage 4 — optional semantic retrieval

Use an offline sentence embedding model over selected redacted fields to recover textually dissimilar cases. It is optional and never bypasses visibility or exact environment filters.

### Stage 5 — fusion and reranking

Use reciprocal rank fusion over independent lists. Apply deterministic compatibility boosts/penalties:

- same exact error code;
- same component/layer;
- compatible architecture/hardware;
- exact build family;
- same symptom class;
- known relation;
- security/visibility admissibility.

Do not use a raw similarity threshold to auto-close as duplicate.

## 7.4 Search result contract

Each result must show:

- case id/title/status/severity;
- relation candidate;
- fused score/rank;
- matched fields and fingerprints;
- environment compatibility;
- strongest supporting evidence;
- root cause and fix, if confirmed;
- relevant refuted hypotheses;
- why it may not apply;
- suggested next check;
- source revision;
- security-safe excerpt only.

Example relation choices the reviewer can record:

```text
same_defect
same_root_cause
same_symptom_different_cause
same_component_only
negative_precedent
unrelated
unknown
```

## 7.5 Mandatory retrieval checkpoints

Run retrieval:

1. at intake normalization;
2. before proposing hypotheses;
3. after a new fingerprint or environment becomes available;
4. after cause confirmation;
5. before knowledge promotion;
6. before closing as duplicate;
7. when an investigation is resumed by a new agent/session.

## 7.6 Evaluation

Build a labeled historical set from existing related bug groups.

Minimum metrics:

- exact-id/error lookup top-1 accuracy;
- duplicate/root-cause `Recall@1`, `Recall@5`, and `Recall@10`;
- mean reciprocal rank;
- nDCG for graded relations;
- fraction of searches with an explanation;
- time to first useful check;
- repeated-refuted-hypothesis rate;
- false duplicate suggestion rate;
- cross-project information leakage rate;
- index build and warm query latency;
- deterministic result stability.

A specific regression suite should use the ZeroKind document family and require the system to retrieve:

- the corrupt-aggregate conclusion;
- the “roaming victims” evidence;
- fixed-but-non-causal sibling defects;
- the refuted producer/unwrap/optional-field hypotheses;
- the expensive reproduction constraints.

---

## 8. Symptom-to-checking strategy

A playbook does not jump from symptom to cause. It defines discriminating observations.

| Symptom class | First discriminators | Minimum capture | High-value next checks |
|---|---|---|---|
| Crash, exception, fatal assert | exact fault type; first failing thread; valid symbols; repeatability | build ID, source/config digest, fault registers, PC/LR/SP, current stack, loaded modules/tasks, reset reason | symbolize; compare normalized stack; validate memory around referenced registers; sanitizer or guarded build; minimize input; inspect prior same-fingerprint cases |
| Hang, deadlock, livelock | CPU idle vs busy; same PC vs changing; blocked wait vs interrupt storm; watchdog stage | per-core PC samples, task states, wait objects, interrupt mask/nesting, queue depths, heartbeat counters, watchdog breadcrumbs | repeated break-in samples; wait-for graph; lock-order trace; interrupt latency; queue producer/consumer deltas; disable one subsystem only through a controlled experiment |
| Timeout or slow path | CPU, I/O, lock, memory, scheduler, external dependency | phase timings, request/run id, queue depth, CPU samples, I/O latency, allocation/RSS, dependency latency | compare known-good baseline; flame/profile; phase binary search; load stratification; resource limits; check whether log silence is caused by buffering |
| Wrong result or data corruption | first boundary where invariant breaks; deterministic vs history-dependent | input/output hashes, invariant ids/values, ownership/generation ids, boundary CRCs, state transitions, build/config | end-to-end checksum checkpoints; component oracle; sanitizer; DMA/cache coherency checks; ordering/fence audit; delta-minimize input |
| Intermittent/flaky/order-sensitive | probability, seed, device/environment strata, temporal clustering | run/boot ids, exact seed/order, timestamps, event ring, environment, occurrence numerator/denominator, capture-loss counters | randomized repeated runs; stress one dimension; schedule perturbation; paired baseline/variant; race/TSan where possible; statistical rate comparison |
| Memory/resource exhaustion | leak vs retained cache vs fragmentation vs burst; bounded vs unbounded | RSS/heap/pool/stack high water, allocation class counters, queue/cache sizes, failure allocation, uptime/workload | ownership census; snapshot deltas; leak sanitizer; pool exhaustion provenance; bounded-load curve; trigger dump before OOM |
| Boot/reset/power failure | reset source; stage reached; persistent corruption; brownout/watchdog/security | reset registers, boot counter, last-stage breadcrumbs, image/build id, bootloader version, power/clock state, persistent crash slot | known-good image; safe boot; stage bisection; power capture; watchdog owner; flash/image integrity; rollback result |
| Protocol/communication | no transmit, no receive, malformed, reordered, timed out, peer reset | endpoint identities, protocol/version, request id, compact packet/event trace, retry counters, clocks | loopback/layer isolation; known-good peer; capture both ends; MTU/framing/endianness; timeout budget; fault injection |
| Storage/data-path | media, controller, DMA, mapping, ordering, recovery, power-loss | command/LBA/namespace, queue ids/head/tail, status, ECC/retry, mapping generation, journal/recovery state, power markers | replay exact workload; read-only identity first; boundary CRCs; FTL/FS layer isolation; power-cut scenario; ECC/threshold distribution analysis |
| Hardware/timing/thermal/EMI | software state vs physical sensitivity | board/SoC/revision, voltage/clock/temp, signal/power measurements, device ids, event timing, firmware build | controlled sweep; known-good board; cable/probe/topology; lower clock; thermal/power correlation; HIL/real-environment repetition |
| Security/permission/isolation | denied as designed vs wrong principal/policy/context | principal, policy/ruleset digest, decision code, resource scope, request id, audit event | reproduce with least privilege; compare policy revisions; check confused-deputy path; preserve secrets outside LLM corpus |
| Unknown/no obvious check | identify the smallest missing distinction | identity bundle, symptom class, known facts, unknowns, prior retrieval results | use the information-gain ladder below; do not add broad logging without a question |

## 8.1 Information-gain ladder for an unclear bug

When no obvious check exists:

1. **Confirm identity**
   - exact source, build, symbols, configuration, environment, hardware, and workload.

2. **Confirm the oracle**
   - what observable distinguishes good from bad?
   - can a positive control prove the channel works?

3. **Classify the failure**
   - crash, hang, incorrect value, timing, resource, protocol, storage, reset, or physical sensitivity.

4. **Find the earliest divergence**
   - place cheap invariant/hash/event checkpoints at architectural boundaries.
   - use binary search over stages, not line-by-line logging.

5. **Choose one competing hypothesis pair**
   - select a check with different predicted outcomes.
   - avoid an experiment that would be compatible with every hypothesis.

6. **Minimize**
   - input, configuration, feature set, concurrency, environment, or commit range.

7. **Escalate capture**
   - minimal snapshot → targeted ring trace → selected memory → hardware trace.
   - escalation is justified by a recorded missing distinction.

8. **Request real-environment evidence**
   - when the decisive state cannot be recreated locally.

Every step emits an evidence record, including “blocked because the required channel does not exist.”

---

## 9. Logging, assertions, and dumps under constrained resources

## 9.1 Four capture tiers

### Tier A — always-on black box

Small, stable, production-safe:

- build ID and configuration digest;
- boot/run/reset identifiers;
- reset/fault reason;
- current task/core;
- critical queue/pool high-water marks;
- a compact last-N event ring;
- watchdog stage breadcrumbs;
- capture drop/truncation counters;
- selected subsystem state generations.

### Tier B — runtime-gated production diagnostics

Compiled in but normally filtered:

- module/instance severity masks;
- first occurrence, first N, power-of-two occurrence, and rate-limited events;
- typed binary event arguments;
- small counters/histograms;
- trigger-on-condition capture;
- on-demand snapshot command with authorization.

### Tier C — diagnostic firmware/software

A distinct build:

- extra invariants/assertions;
- selected memory regions;
- broader thread/task dumps;
- queue/ownership tracing;
- shadow metadata;
- sanitizers/guard allocators where target resources allow;
- deterministic scheduling or fault injection.

### Tier D — lab trace

High-cost, targeted:

- T32/CoreSight/ETM/ITM/SWD/JTAG trace;
- bus/protocol analyzer;
- high-rate packet or event capture;
- power/thermal/signal capture;
- intrusive breakpoints/watchpoints.

## 9.2 Compact event format

Prefer fixed binary records:

```text
event_id | timestamp_delta | core/task | arg_type_bitmap | arg0 | arg1
```

The exact dictionary is stored with the build artifacts. The target sends IDs and typed values; the host expands names and formatting.

Required metadata:

- schema version;
- endian/word size;
- clock source/frequency and wrap behavior;
- ring generation;
- dropped/overwritten count;
- build/event-dictionary id;
- boot/run id;
- checksum or consistency marker.

## 9.3 Ring and sampling policy

Use bounded policies:

- overwrite-oldest for rolling context, unless first-failure preservation is more important;
- freeze-on-trigger with pre/post trigger allocation;
- first occurrence for invariant violations;
- first N plus power-of-two samples for repetitive faults;
- token-bucket/rate limit for bursty logs;
- per-call-site counters;
- periodic aggregates instead of one event per operation;
- deterministic sampling where run comparison is required.

Record the chosen policy; otherwise absence may be misinterpreted.

## 9.4 Assertion policy

An assertion should capture:

- stable invariant id;
- expected relation;
- relevant actual values;
- component/layer;
- object/generation ids;
- current state/event;
- source/build id;
- whether execution is safe to continue.

Rules:

- compile-time assertions for static invariants;
- production runtime assertions only where failure handling is safe and defined;
- no dynamic allocation or general formatter in fatal context;
- no unbounded traversal of possibly corrupted structures;
- validate pointers/ranges before dereference;
- preserve first failure where later execution can destroy evidence;
- distinguish fatal safety assertions from diagnostic assertions;
- every disabled assertion category is visible in the build manifest.

## 9.5 Persistent crash area

For firmware:

- two-slot or journaled record;
- magic, version, generation, length, CRC/hash;
- write header/contents/commit marker in an order resilient to reset;
- never overwrite the only valid prior crash until the new record commits;
- boot reads and uploads/copies before clearing;
- privacy/security policy applies;
- storage wear and worst-case write time are budgeted.

## 9.6 Instrumentation budget

Every probe/diagnostic feature declares:

- code/flash bytes;
- static RAM;
- worst-case stack;
- cycles/latency;
- bandwidth;
- storage writes;
- interrupt masking;
- timing perturbation;
- privacy/security content;
- target lifetime (`always`, `temporary`, `lab-only`);
- removal or retention decision after closure.

A probe that materially changes scheduling or timing cannot be treated as observationally neutral.

---

## 10. Reproduction, real environment, and firmware variants

## 10.1 Reproduction levels

| Level | Environment | Purpose |
|---|---|---|
| R0 | static inspection/retrieval | identify known cases and missing evidence |
| R1 | unit/component/model | cheapest deterministic causal oracle |
| R2 | process/integration/full software | preserve real subsystem interaction |
| R3 | simulator/emulator/digital twin | architecture/firmware path without physical target |
| R4 | HIL/lab target | real device with controlled environment |
| R5 | field/customer/production-equivalent | physical state, fleet history, or environment not recreatable elsewhere |

A case can have several scenario results. “Reproduced” always names the level and exact oracle.

## 10.2 Prefer local reproduction when

- the required input/state can be captured and legally transferred;
- the environment can be represented accurately enough;
- a component or simulator oracle is causal;
- iteration speed or instrumentation is important;
- the failure does not depend on unique physical degradation/history.

## 10.3 Request real-environment execution when

- the failure depends on device-specific wear, retention, power, temperature, analog margins, signal integrity, attached hardware, fleet history, or confidential data that cannot leave the site;
- a simulator/HIL mismatch remains plausible;
- the failure is too rare to reproduce economically in one lab;
- reproducing locally would be unsafe;
- a fix must be verified against the exact deployment environment;
- the evidence channel itself must be tested.

The request must be a generated `RemoteDebugRequestV1`, not a vague “send more logs.”

It includes:

- exact case/build/scenario ids;
- why local evidence is insufficient;
- requested commands/scripts;
- safety and privacy limits;
- expected duration/run count;
- required artifacts;
- positive control;
- upload destination/expiry;
- rollback;
- stop conditions;
- how success/failure will be judged.

## 10.4 Are multiple firmware builds needed?

**Not by default.**

Prefer one baseline image plus runtime-gated diagnostics when all of these hold:

- diagnostics do not change timing or memory layout enough to affect the bug;
- access is authenticated;
- feature gates and configuration are captured;
- the same symbols/build identity can decode every mode;
- a bad setting cannot violate safety.

Use multiple images when:

- the failure is timing/layout sensitive;
- the required instrumentation exceeds the production budget;
- safety policy forbids dormant diagnostics;
- compile-time feature isolation is the experiment;
- the field turnaround is expensive and a bounded diagnostic pack gives substantially more information.

### Bounded diagnostic pack

A normal pack is:

1. **B — exact baseline**
2. **O — observability-only**, no intended behavior change
3. **H1/H2 — one or two orthogonal hypothesis variants**
4. **F — fix candidate**, only after causal support

Do not send ten speculative builds. Cap the pack through project policy, normally three diagnostic variants plus baseline.

Each image requires:

- unique build ID and content hash;
- source commit/dirty state;
- configuration and feature digest;
- exact symbols/event dictionary;
- signed manifest where applicable;
- compatibility and rollback instructions;
- predicted result table;
- randomized or counterbalanced run order when order/environment drift matters.

Never combine several behavioral changes in one hypothesis variant.

## 10.5 Feature disabling and delta experiments

Feature-off experiments are useful only when:

- the disabled feature is represented as one explicit independent variable;
- the oracle still exercises the relevant path;
- dependencies and configuration changes are captured;
- the result is not mistaken for a fix.

Use:

- binary/config delta debugging for a large independent feature set;
- hierarchical bisection by subsystem/layer;
- pairwise/fractional designs when interactions are plausible;
- commit bisection when a stable automated good/bad oracle exists.

A “bug disappears with feature X off” result supports an involvement relation. It does not by itself identify the root cause.

---

## 11. Evidence intake and automatic artifact handling

## 11.1 Event-driven plus reconciliation

Recommended trigger model:

- GitHub issue/comment/workflow webhooks;
- Jira issue/attachment webhooks;
- Microsoft Graph change notifications for the monitored mailbox;
- CI result events;
- MinIO/S3 object notifications where available;
- periodic reconciliation using source delta/cursor APIs;
- daily digest as a generated summary, not the ingestion authority.

## 11.2 Durable inbox

Before parsing:

- verify source signature/authentication;
- assign/source immutable delivery id;
- store raw payload hash and receive time;
- deduplicate retries;
- acknowledge only after durable persistence;
- maintain retry and dead-letter/quarantine states;
- never advance a source cursor past an unadmitted item;
- reconcile gaps and expired subscriptions;
- paginate to completion;
- record source clock and collector clock.

## 11.3 Auto-download decision

The system may automatically fetch an artifact only if:

- source provider and host are allowlisted;
- authentication is available through a secret manager;
- the URL/object reference has not expired;
- metadata can be read first;
- object size is within policy;
- version/ETag/object id is pinned;
- security classification permits local retrieval;
- the case scope authorizes it.

Do not trust URL suffixes.

### Safe processing sequence

1. fetch metadata/stat;
2. admit expected size/type/owner/version;
3. download into quarantine with no execute permission;
4. stream SHA-256 while downloading;
5. verify content length and object version;
6. detect magic/MIME independently;
7. reject or sandbox archives; enforce recursion and expansion limits;
8. malware/secret scan according to environment;
9. store immutable raw object;
10. create artifact row;
11. run parser in a read-only, no-network, CPU/memory/time-limited sandbox;
12. store derived output separately with parser receipt;
13. redact before LLM indexing;
14. bind to exact build/symbol set or mark analysis `BLOCKED_SYMBOL_MISMATCH`.

## 11.4 Evidence bundle

Every intake or capture produces `EvidenceBundleV1`:

- case/source ids;
- capture and receive times with clock basis;
- app/FW/product versions;
- source commit and dirty digest;
- executable build ID and content hash;
- symbol/event dictionary ids;
- toolchain/config/feature digests;
- OS/kernel/container/rootfs;
- board/SoC/revision/bootloader;
- run/boot/device pseudonym;
- reset reason and uptime;
- environment/workload/seed;
- artifact list with hash/size/type;
- parser tool/version/command/config/result;
- redaction/security/retention;
- signature/provenance;
- completeness and known gaps.

## 11.5 Parser/tool registry

The knowledge base should map artifact types to approved parsers and required inputs:

| Artifact | Typical parser | Compatibility requirement |
|---|---|---|
| ELF/core | `readelf`, `eu-readelf`, GDB batch, systemd coredump tools | exact executable/shared-library build ids and symbols |
| PDB/minidump | WinDbg/cdb or approved minidump processor | exact module ids/PDBs |
| Breakpad/Crashpad dump | stackwalker/minidump processor | exact module symbol ids |
| Zephyr coredump | Zephyr parser + coredump GDB server | matching Zephyr ELF and format version |
| ESP-IDF coredump | `idf.py coredump-info/debug` / esp-coredump | matching app ELF SHA/build |
| T32 trace/dump | reviewed PRACTICE script and host decoder | target config, ELF, trace clock |
| Binary event log | build event dictionary decoder | exact dictionary/build id |
| Firmware image | format/manifest inspector only by default | board/product/slot compatibility |
| NAND/statistical dataset | validated schema loader + analysis script | units, hierarchy, sampling metadata |

Every parser output carries:

- input hashes;
- tool binary/version hash;
- command/arguments;
- configuration;
- start/end time;
- exit/verdict;
- stdout/stderr hashes;
- produced artifact hashes;
- warnings and unsupported fields.

## 11.6 Direct fixes to the current daily-debug driver

1. Replace timestamp placeholders with real RFC 3339 UTC and local display conversion.
2. Use provider delta/cursor APIs rather than `now - 24h`.
3. Fetch full messages and attachment metadata, not only previews.
4. Implement complete pagination.
5. Separate `NO_MESSAGES` from `FETCH_FAILED`.
6. Do not save the cursor/watermark on partial/failing fetch or parse.
7. Add durable inbox/event receipts before digest generation.
8. Replace suffix classification with metadata + magic classification.
9. Add allowlist, size, quarantine, hashing, and parser-sandbox policy.
10. Generate a per-event/case evidence manifest.
11. Add webhook/change-notification adapters and subscription health checks.
12. Keep daily polling as reconciliation.
13. Make `--dry-run` produce the complete admission/capture plan without fetching bytes.
14. Add source-specific idempotency tests and retry tests.
15. Link admitted cases to V2 rather than only writing a dated Markdown digest.

---

## 12. Verification scenario and firmware generation

## 12.1 Scenario contract

A `VerificationScenarioV1` contains:

- `scenario_uid`
- case and hypothesis ids
- reproduction level
- purpose (`reproduce`, `discriminate`, `regression`, `closure`)
- preconditions
- exact source/build/config/environment
- baseline and variants
- setup
- stimulus/workload/fault injection
- oracle and positive control
- expected outcome per hypothesis
- required capture tier and event/assert ids
- timeout/hang detection
- repetitions, seeds, randomization, blocking
- safety limits and prohibited operations
- cleanup/recovery
- rollback image/path
- executor/tool/script ids and versions
- evidence output contract
- escalation condition
- pass/fail/blocked rules

## 12.2 Generation algorithm

The LLM can draft a scenario from the selected playbook:

1. parse the observation and unknowns;
2. retrieve similar cases and negative precedents;
3. select one hypothesis distinction;
4. choose the lowest reproduction level that can expose it;
5. define an independent oracle and positive control;
6. select the minimum capture tier;
7. calculate the instrumentation budget;
8. decide one image vs bounded variants;
9. attach scripts/tool recipes by stable knowledge id;
10. produce safety/rollback/stop conditions;
11. require review before any hardware-mutating step;
12. execute only through authorized adapters;
13. append results and update retrieval immediately.

## 12.3 Verification ladder after a fix

1. exact reduced reproducer;
2. sibling/similar-case tests;
3. owning component/layer test;
4. affected integration/system tests;
5. affected firmware/HIL scenario;
6. clean full build and requested full suite;
7. exact real-environment verification when required;
8. recurrence-rate or observation-window check for intermittent cases;
9. verify diagnostics did not create unacceptable overhead;
10. promote reusable knowledge.

A fix is not closed merely because the original test passes. The closure claim records exactly which ladder levels passed and which remain blocked.

---

## 13. Statistical analysis policy

## 13.1 Trigger conditions

Use statistics when at least one applies:

- intermittent occurrence rate;
- noisy latency/performance;
- repeated A/B firmware runs;
- population/fleet variability;
- device/lot/die/block/page heterogeneity;
- time, wear, retention, read-disturb, or temperature drift;
- threshold-voltage or ECC distributions;
- multimodal response;
- probabilistic fault injection;
- rare-event reliability.

Do not require statistics for a deterministic one-run crash with a reliable causal oracle.

## 13.2 Analysis ladder

1. **Integrity**
   - schema, units, hashes, duplicates, truncation, missingness, censoring, capture bias.

2. **Stratification**
   - architecture/build/device/lot/die/plane/block/page/wordline/state, workload, temperature, wear, retention, time.

3. **Descriptive**
   - count, rate, confidence interval, median/IQR, robust spread, quantiles/tails, ECDF, histogram, time sequence.

4. **Comparison**
   - paired vs independent design;
   - effect size and uncertainty;
   - distribution distance;
   - rate ratio/difference;
   - nonparametric/robust methods if assumptions fail.

5. **Drift/change**
   - control chart, EWMA/CUSUM, change-point analysis, seasonal/workload adjustment.

6. **Mixture/multimodality**
   - only after physical/population stratification;
   - compare model orders and stability;
   - record that a statistical component is not automatically a physical defect group.

7. **Confirmation**
   - preregistered scenario, randomized/counterbalanced order, held-out data, stopping rule, multiple-comparison control.

## 13.3 SSD/NAND cell-distribution analysis

For NAND threshold/cell distributions, capture or derive:

- technology/mode and expected program-state count;
- die/plane/block/page/wordline/layer/state;
- open/closed block and program pattern;
- P/E count;
- retention age and temperature history;
- read-disturb count;
- read-reference and read-retry settings;
- raw read counts/soft information;
- ECC correction count, syndrome or RBER where available;
- sample count and excluded cells/pages;
- controller/FW build and calibration state.

Analyze:

- center/location shift;
- spread;
- skew/tails;
- adjacent-state overlap;
- BER/ECC margin;
- reference-voltage optimum;
- mode count and component stability;
- drift over wear/retention/disturb/time;
- between-layer/page/block/device variability.

### Group-count rule

Do not hard-code one grouping assumption.

- NAND logical states commonly imply `2/4/8/16` levels for SLC/MLC/TLC/QLC.
- A project-specific analysis may intentionally test `1/2/4/16` groups or other expected structures.
- Store the allowed component counts and domain interpretation in the analysis specification.
- Compare alternatives; do not force every small bump to become a component.
- Require minimum weight/separation/stability and physical consistency before naming a group.
- Preserve an “unexplained residual/noise” class.

### Recommended output for LLM analysis

- machine-readable summary table;
- normalized numeric series;
- component candidates with center/spread/weight/overlap/stability;
- fit/residual metrics;
- stratification metadata;
- time/wear trend;
- uncertainty;
- graph image plus a text representation of peaks, valleys, crossings, and tails;
- explicit warnings about pooled heterogeneous populations.

---

## 14. Common SPipe knowledge and project-local wiki

## 14.1 Canonical common layout

Proposed SPipe source tree:

```text
knowledge/
  common/
    debug/
      ontology.sdn
      symptom_aliases.sdn
      check_strategies.sdn
      capture_profiles.sdn
      artifact_types.sdn
      evidence_rules.sdn
      reproduction_levels.sdn
      statistics.sdn
      tool_registry.sdn
      playbooks/
        crash.sdn
        hang.sdn
        corruption.sdn
        intermittent.sdn
        performance.sdn
        resource.sdn
        boot_reset.sdn
        protocol.sdn
        storage.sdn
        hardware_environment.sdn
skill_src/
  debug/
    common.md
    software.md
    firmware.md
    statistics.md
```

Generated projections:

```text
plugin/skills/debug-common/SKILL.md
plugin/skills/debug-software/SKILL.md
plugin/skills/debug-firmware/SKILL.md
plugin/skills/debug-statistics/SKILL.md
.claude/skills/...
.codex/skills/...
.gemini/skills/...
```

There must be one canonical source. Existing duplicate agent/skill copies should be generated or thin references.

## 14.2 Project-local layout

In a host project:

```text
.spipe/
  debug/
    config.sdn
    aliases.sdn
    approved_tools.sdn
    capture_profiles.sdn
    local_playbooks/
    remote_env_profiles/
doc/00_llm_process/
  llm_wiki.md              # generated project overlay/index
  debug/
    local_notes/           # canonical only when policy says so
```


Project configuration pins:

- common SPipe revision;
- knowledge schema version;
- allowed common namespaces;
- project aliases;
- privacy/visibility partitions;
- approved tools and remote adapters;
- artifact size/retention;
- default capture budgets;
- firmware-variant cap;
- safety policy;
- local promotion policy.

## 14.3 Reference and precedence rules

Resolution order:

1. exact project case evidence;
2. project-local reviewed playbook;
3. pinned common SPipe playbook;
4. external research/reference.

A local playbook may specialize applicability or add checks. It cannot silently remove:

- evidence identity requirements;
- privacy/security controls;
- hardware safety gates;
- symbol/build compatibility;
- append-only evidence;
- fail-closed verdict semantics.

References use stable knowledge UIDs and compatible major versions, not copied paragraphs or fragile relative paths.

Example:

```text
extends:
  - dbgk:common:firmware-crash:1
  - dbgk:common:tiered-capture:1
uses_tools:
  - dbgk:tool:t32-trace-capture:1
local_additions:
  - dbgk:project-simple:stage3-bootstrap-env:1
```

## 14.4 Generated LLM wiki

The local LLM wiki should present virtual views such as:

- **Symptom → first checks**
- **Error/assert id → prior cases**
- **Component/layer → recurring causes**
- **Artifact type → approved parser**
- **Environment → capture script**
- **Open investigation → next discriminating check**
- **Refuted hypothesis → do-not-repeat condition**
- **Cause → verification tests**
- **Firmware target → capture budgets and rollback**
- **Statistics trigger → analysis recipe**
- **Common knowledge update available**
- **Broken/stale knowledge references**

Wiki entries show source UID/revision and whether content is common or local. Editing a generated page is rejected with a pointer to the canonical record or proposal command.

## 14.5 User/project updates to common knowledge

Commands:

```text
spipe debug knowledge propose <case-or-local-playbook>
spipe debug knowledge lint <proposal>
spipe debug knowledge review <proposal>
spipe debug knowledge promote <proposal>
spipe debug knowledge update
spipe debug knowledge diff <old-revision> <new-revision>
```

Promotion requirements:

- provenance and source case links;
- confidential details removed;
- applicability and exclusions;
- stable symptom/check/result vocabulary;
- evidence quality;
- safety review where hardware/firmware is involved;
- regression examples;
- schema/skill generation tests;
- reviewer identity.

Default evidence threshold:

- two independent cause-confirmed cases, or
- one exceptionally strong cause-confirmed case with a reusable invariant/tool rule.

Refuted and unsafe approaches are also promotable when their scope is clear.

Host projects pin common revisions and update explicitly. An update produces a semantic diff and identifies local overrides affected by the change.

---

## 15. Skill behavior

## 15.1 `debug-common`

Mandatory sequence:

1. create/resume case;
2. capture identity;
3. normalize observation;
4. retrieve prior cases/playbooks/negative precedents;
5. identify unknowns;
6. choose one discriminating check;
7. create capture or scenario plan;
8. execute locally or generate a remote request;
9. admit and parse evidence;
10. record result;
11. update hypotheses;
12. link fix and verification;
13. promote reusable knowledge.

Hard rules:

- never claim PASS from absent output;
- never symbolize with mismatched binaries;
- never repeat a refuted hypothesis without satisfying its rerun condition;
- never treat “bug disappeared” as a cause;
- never edit generated wiki or raw SDN;
- never execute downloaded artifacts;
- never enable broad instrumentation without a budget and question;
- always preserve exact commands, tool versions, seeds, and hashes.

## 15.2 `debug-software`

Adds:

- core/minidump processing;
- sanitizers;
- deterministic repro reduction;
- fuzzing;
- commit bisection;
- process/thread/lock profiling;
- service/environment capture;
- affected-test and full-suite closure.

## 15.3 `debug-firmware`

Extends `debug-common` and references `debug-software` where host tools apply. Adds:

- reset/boot identity;
- crash slots;
- compact event ring;
- hardware debug;
- HIL/real-environment levels;
- power/timing/thermal state;
- image compatibility;
- diagnostic pack rules;
- flash authorization, rollback, and stop conditions;
- target capture budgets;
- firmware/system verification.

## 15.4 `debug-statistics`

Adds:

- trigger decision;
- analysis-plan contract;
- sampling/stratification;
- repeated-run and A/B design;
- control/drift analysis;
- distribution and mixture safeguards;
- storage/NAND-specific hierarchy;
- machine-readable and image-to-text outputs.

---

## 16. Proposed CLI and MCP surface

## 16.1 CLI

```text
spipe bug ingest <source>
spipe bug normalize <case>
spipe bug show <case>
spipe bug search <query-or-case> [--explain]
spipe bug relate <case> <other> --kind <relation>
spipe bug plan <case>
spipe bug capture-plan <case>
spipe bug request-data <case> --environment <profile>
spipe bug evidence fetch <reference>
spipe bug evidence verify <bundle>
spipe bug evidence parse <evidence>
spipe bug hypothesis add <case>
spipe bug hypothesis test <case> <hypothesis>
spipe bug scenario generate <case> <hypothesis>
spipe bug scenario run <scenario>
spipe bug variant-plan <scenario>
spipe bug verify <case>
spipe bug close <case>
spipe debug knowledge propose|lint|review|promote|update|diff
spipe bug reindex
spipe bug doctor
spipe bug metrics
```

All mutation commands return a revision/receipt and support plan/dry-run mode where meaningful.

## 16.2 MCP resources

```text
spipe://bugs/{bug_uid}
spipe://bugs/{bug_uid}/observations
spipe://bugs/{bug_uid}/hypotheses
spipe://bugs/{bug_uid}/experiments
spipe://bugs/{bug_uid}/evidence
spipe://bugs/{bug_uid}/verification
spipe://debug/symptoms/{class}
spipe://debug/playbooks/{knowledge_uid}
spipe://debug/tools/{knowledge_uid}
spipe://evidence/{evidence_uid}/manifest
spipe://search/bugs?snapshot=...&query=...
```

## 16.3 MCP tools

- case create/update through typed commands;
- add immutable observation/evidence/hypothesis result;
- search similar with explanation;
- generate capture/scenario/variant/remote request;
- verify evidence/build compatibility;
- invoke approved parser;
- record verification claim;
- propose common knowledge.

MCP must call the same services as CLI. No duplicated SDN parsing or business logic.

---

## 17. Normative bug-management policy

The following is the proposed policy text for SPipe.

### 17.1 Intake

- Every report **MUST** receive a stable case UID and source receipt.
- External issue, email, CI, and artifact ids **MUST** be retained.
- A case **MUST NOT** be marked normalized until source/build/environment completeness is assessed.
- Intake cursors **MUST NOT** advance over unpersisted or failed events.
- Downloaded artifacts **MUST** be quarantined, hashed, classified by content, and treated as untrusted.

### 17.2 Retrieval

- Similar-case lookup **MUST** run before initial root-cause proposals and whenever a new fingerprint is obtained.
- Results **MUST** include negative precedents and explain match signals.
- Similarity **MUST NOT** automatically establish duplicate or same cause.
- Retrieval **MUST** enforce project and security visibility before scoring.

### 17.3 Investigation

- Hypotheses **MUST** state predicted observations.
- A check **SHOULD** distinguish at least two live hypotheses.
- Evidence **MUST** record exact build, environment, command/scenario, tool, and result.
- Negative evidence **MUST** prove the observation channel was valid.
- Refuted hypotheses **MUST** record rerun conditions.
- LLM session memory **MUST NOT** be the only repository of investigation state.

### 17.4 Instrumentation

- Every probe **MUST** have a resource/timing/privacy budget.
- Fatal capture **MUST** be bounded and avoid unsafe allocation/formatting/traversal.
- Diagnostic builds **MUST** have unique build IDs and matching decoders/symbols.
- Log filtering/sampling/drop policy **MUST** be recorded.
- Missing or truncated output **MUST NOT** be treated as a negative result.

### 17.5 Reproduction and variants

- Reproduction **MUST** name level, environment, oracle, and evidence.
- The lowest adequate reproduction level **SHOULD** be used first.
- Real-environment requests **MUST** be explicit, bounded, safe, and machine-readable.
- Multiple firmware builds **MUST NOT** be created without an experiment matrix.
- Each variant **MUST** change one declared variable unless a designed interaction experiment says otherwise.
- Baseline, symbols, manifest, rollback, and stop conditions **MUST** accompany a firmware pack.

### 17.6 Fix and verification

- A disappearing symptom **MUST NOT** alone establish cause.
- A fix **MUST** link to the causal hypothesis and exact code/config change.
- Verification **MUST** begin at the smallest causal layer and close affected/full layers as required.
- PASS/FAIL/BLOCKED/INCONCLUSIVE **MUST** be explicit.
- Closure **MUST** record exclusions and unresolved risks.
- Reusable learning **SHOULD** be proposed for common knowledge after closure.

### 17.7 Statistics

- Statistical work **MUST** declare question, population, sampling unit, strata, and missing-data policy.
- Exploratory and confirmatory results **MUST** be distinguished.
- Heterogeneous physical populations **MUST** be stratified before mixture interpretation.
- Effect size/uncertainty **SHOULD** accompany significance tests.
- A fitted component **MUST NOT** automatically be called a physical defect group.

---

## 18. File-by-file implementation map

## 18.1 SPipe repository

### Add

```text
knowledge/common/debug/**
skill_src/debug/common.md
skill_src/debug/software.md
skill_src/debug/firmware.md
skill_src/debug/statistics.md
doc/00_llm_process/spipe/bug_management_policy.md
doc/00_llm_process/spipe/debug_knowledge_architecture.md
doc/00_llm_process/spipe/evidence_intake.md
doc/00_llm_process/spipe/remote_debug_request.md
doc/00_llm_process/spipe/statistical_debugging.md
plugin/skills/debug-common/SKILL.md             # generated
plugin/skills/debug-software/SKILL.md           # generated
plugin/skills/debug-firmware/SKILL.md           # generated
plugin/skills/debug-statistics/SKILL.md         # generated
```

### Refactor

```text
.claude/agents/debug.md
.claude/skills/lib/debug.md
.claude/skills/lib/t32.md
.claude/skills/spipe_loop.md
doc/00_llm_process/skill_command/skills/pipe/verify/bug_review/skill.md
plugin/skills/spipe-loop/SKILL.md
README.md
scripts/setup-spipe-links.sh
scripts/setup-spipe-links.ps1
cli/spipe.js
mcp/server.js
```

Refactor these into generated projections or thin references to canonical skill sources.

### Add CLI/MCP modules

```text
src-or-equivalent/debug/case_service
src-or-equivalent/debug/knowledge_registry
src-or-equivalent/debug/retrieval
src-or-equivalent/debug/evidence
src-or-equivalent/debug/scenario
src-or-equivalent/debug/intake
src-or-equivalent/debug/statistics
```

Use the project’s accepted implementation language/layout when the code wave begins; the paths above describe ownership, not a forced language choice.

## 18.2 Simple repository

### Database/API

```text
src/lib/nogc_sync_mut/database/bug_case_v2/**
src/lib/common/debug_schema/**
src/app/bug/**
src/lib/nogc_async_mut/mcp/bugdb_resource.spl
doc/08_tracking/bug/bug_db_v2.sdn
```

Actions:

- implement V2 typed tables and transactional service;
- remove manual MCP parsing;
- add full CLI/MCP parity;
- add migration and consistency tools;
- generate recent/open/relationship/wiki views.

### Search projection

```text
src/lib/common/search/**
src/app/spipe_knowledge_compiler/**
```

Actions:

- project bug cases/evidence/playbooks to scoped fielded documents;
- add exact fingerprint indexes;
- add relation graph projection;
- add optional semantic provider;
- add historical retrieval evaluation;
- gate BM25 activation on current correctness bugs.

### Intake

```text
src/app/devhub/cmd_daily_debug.spl
src/app/devhub/adapter_outlook_*
src/app/devhub/adapter_jira_*
src/app/devhub/adapter_github_*
src/app/devhub/adapter_minio_*
```

Actions:

- durable inbox;
- full pagination and delta cursors;
- event subscriptions/webhooks;
- no cursor advance on partial failure;
- evidence bundle and quarantine pipeline;
- real RFC 3339/date handling;
- source-specific adapters and receipts.

### Firmware/debug infrastructure

Reuse and extend:

```text
src/lib/**/debug/**
src/lib/**/logging/**
src/lib/**/dump/**
src/lib/**/event/**
src/app/**/t32*
scripts/**/t32*
```

Add:

- compact event dictionary/build binding;
- crash slot;
- capture profiles;
- scenario runner;
- variant manifest;
- parser receipts;
- HIL/remote request integration.

---

## 19. Parallel implementation plan

## 19.1 Dependency order

```text
Wave 0: freeze contracts and corpus
Wave 1: V2 store + migration
Wave 2: evidence manifest/vault + parser receipts
Wave 3: projection/search + wiki
Wave 4: skills and planner
Wave 5: intake/webhook/reconciliation
Wave 6: firmware capture/variants/HIL
Wave 7: statistics
Wave 8: end-to-end hardening and cutover
```

## 19.2 Agent allocation

### Agent A — schema and authority

Owns:

- V2 enums/records/tables;
- append-only audit;
- transaction/integrity rules;
- migration contract;
- V1 compatibility.

Must not modify search or intake adapters except interfaces.

### Agent B — migration and corpus labeling

Owns:

- V1/Markdown importer;
- provenance;
- conflict reports;
- historical related-case labels;
- ZeroKind regression corpus.

Runs after Agent A freezes schema.

### Agent C — evidence vault and parser sandbox

Owns:

- `EvidenceBundleV1`;
- quarantine/hash/type;
- immutable locators;
- parser registry/receipts;
- symbol/build gate;
- redaction boundary.

### Agent D — retrieval

Owns:

- exact indexes;
- fielded projection;
- fingerprints;
- graph;
- optional semantic lane;
- fusion/explanations;
- quality metrics.

Must test against Agent B corpus and current BM25 defects.

### Agent E — common knowledge and skills

Owns:

- ontology/playbooks;
- canonical skill source;
- generated projections;
- common/local reference resolution;
- promotion workflow.

Consumes stable schemas from A/C/D.

### Agent F — intake and scheduling

Owns:

- durable inbox;
- GitHub/Jira/Graph adapters;
- webhook/change notification;
- polling/delta reconciliation;
- cursor/idempotency;
- daily digest projection;
- MinIO metadata-first retrieval.

### Agent G — software debugging executors

Owns:

- core/minidump recipes;
- sanitizer/fuzz/bisect/delta;
- script registry;
- scenario adapter for host software/compiler/service.

### Agent H — firmware/HIL

Owns:

- compact event ring;
- crash slot;
- capture profiles;
- T32/OpenOCD/GDB adapter references;
- diagnostic pack/variant manifests;
- remote environment requests;
- safety/rollback.

### Agent I — statistics/storage analysis

Owns:

- stats trigger/plans;
- repeated-run rate analysis;
- control/EWMA;
- distribution/mixture safeguards;
- NAND hierarchy and graph/text outputs.

### Agent J — integration and adversarial review

Owns:

- CLI/MCP parity;
- generated wiki;
- permission/visibility;
- untrusted artifact tests;
- recovery/fault injection;
- performance;
- end-to-end acceptance and cutover.

## 19.3 Parallel-work rules

- Each agent uses an isolated worktree/branch and explicit owned paths.
- Schema/interface changes are proposed through small reviewed commits.
- No agent edits generated files as canonical source.
- Tests land with each contract.
- Migration/import and index builds are deterministic and resumable.
- Cross-agent fixtures are versioned.
- Integration merges structural moves separately from semantic changes.
- Failed shards are rerun first; then affected closure; then one clean full closure.
- A maximum of three fix/verify cycles per integration wave before recording a blocker and re-planning.

---

## 20. Test and acceptance plan

## 20.1 Database

- V1 import is idempotent.
- All V1 records and source documents retain provenance.
- CRC/integrity failure is explicit; no silent empty DB.
- Unknown mandatory enums fail.
- Concurrent writers serialize through the owner.
- Append-only rows cannot be rewritten without a superseding event.
- CLI/MCP/database API return the same fields and revisions.
- Generated Markdown round-trips to no canonical mutation.

## 20.2 Retrieval

- exact id/error/artifact hash returns top 1;
- normalized stack matches across ASLR;
- incompatible builds/hardware are visibly penalized;
- refuted hypotheses appear;
- result explanations name fields/fingerprints;
- visibility tests show zero cross-scope leakage;
- deterministic no-embedding mode is stable;
- semantic lane improves recall on labeled dissimilar cases without unacceptable false duplicates;
- ZeroKind family regression passes;
- open BM25 aliasing cases are fixed or the affected provider remains disabled.

## 20.3 Intake

- duplicate webhook delivery is admitted once;
- out-of-order events reconcile;
- page > 50 is complete;
- failed page/parse/download does not advance cursor;
- expired subscription is renewed and gap-reconciled;
- invalid signature is rejected;
- URL extension/type mismatch is quarantined;
- oversized/archive-bomb artifact is rejected;
- parser cannot access network/write source/escape limits;
- raw and derived hashes are stable;
- missing symbols produce BLOCKED, not guessed analysis;
- dry-run has zero side effects.

## 20.4 Firmware

- crash slot survives reset during each write phase;
- old valid record remains if new record is incomplete;
- event ring wrap/drop counters decode;
- wrong event dictionary/build is rejected;
- fatal handler meets stack/time budget;
- baseline and observability-only variants are manifest-distinct;
- unauthorized flash is blocked;
- rollback and stop conditions are exercised;
- HIL result captures exact target identity.

## 20.5 Statistics

- duplicate/missing/censored samples detected;
- strata cannot be accidentally pooled;
- deterministic input yields no unnecessary mixture;
- synthetic multimodal fixtures recover allowed modes within tolerance;
- tiny unstable components are labeled residual/noise;
- randomized A/B analysis preserves run order and seed;
- EWMA/control outputs reproduce known fixtures;
- NAND output includes center/spread/tail/overlap/state hierarchy and uncertainty.

## 20.6 Skill/wiki

- firmware skill resolves and extends common skill;
- local project wiki resolves pinned common UIDs;
- stale/broken refs fail lint;
- generated views are deterministic;
- editing a generated page is rejected with the canonical command;
- promotion removes secrets and retains provenance;
- a common update shows semantic diff and affected overrides.

## 20.7 Acceptance criteria

The first useful release is accepted when:

1. a new bug report creates a V2 case and identity-bound evidence request;
2. similar-bug search returns explainable exact/lexical results;
3. an LLM follows a symptom playbook and records one discriminating experiment;
4. a dump/log is safely admitted, hashed, parsed, and symbol-bound;
5. a firmware case can generate a bounded baseline/observability/variant plan;
6. a remote-environment request is machine-readable;
7. the local wiki references pinned common knowledge;
8. a closed case can propose a reviewed common playbook;
9. current V1 cases remain readable with migration provenance;
10. no provider failure, malformed DB, symbol mismatch, or absent output can produce a false PASS.

---

## 21. Rollout recommendation

### Release 1 — reliable case memory

- V2 store, migration, append-only evidence/hypotheses;
- exact retrieval;
- generated case views;
- common debug skill with mandatory retrieval and negative-evidence rules;
- no auto-download yet.

### Release 2 — evidence and lexical retrieval

- evidence bundle/vault;
- safe parser receipts;
- build/symbol gate;
- fielded lexical search and explanations;
- project/common wiki references.

### Release 3 — event-driven intake

- durable inbox;
- webhooks/change notifications;
- delta reconciliation;
- safe artifact fetching;
- daily digest as projection.

### Release 4 — firmware orchestration

- capture profiles;
- crash/event infrastructure;
- scenario generation;
- bounded diagnostic packs;
- T32/OpenOCD/HIL/remote request integration.

### Release 5 — advanced retrieval and statistics

- structural/graph fusion;
- optional semantic retrieval;
- statistics plans and storage/NAND analysis;
- retrieval/diagnosis quality dashboards.

This sequence gives immediate value without waiting for the full knowledge compiler or embedding infrastructure.

---

## 22. Key risks and mitigations

| Risk | Mitigation |
|---|---|
| DB becomes too verbose | normalize stable fields; store raw bytes externally; generate concise views |
| LLM writes unsupported conclusions | append-only evidence and explicit claim/verdict contracts |
| Search returns superficially similar bugs | environment/fingerprint compatibility, explanations, manual relation decision |
| Repeated bad hypotheses | first-class refutation and mandatory negative-precedent retrieval |
| Diagnostic firmware changes the bug | instrumentation budget, observability-only lane, separate builds for timing-sensitive cases |
| Too many firmware variants | bounded pack and experiment matrix |
| Inbox loses events | durable receipt, idempotency, no cursor advance on failure, reconciliation |
| Malicious/huge attachments | allowlist, metadata first, quarantine, size/type/archive limits, parser sandbox |
| Wrong symbols create false analysis | build-id/content binding and BLOCKED verdict |
| Common knowledge leaks project details | explicit proposal/redaction/review/pinned revision |
| Generated skills drift | canonical `skill_src` and projection tests |
| BM25 defects corrupt retrieval | historical fixtures and provider gate |
| Statistics invent groups | stratification, model stability, minimum component criteria, residual class |
| Wiki becomes stale | generated views bound to store/index revisions and broken-ref lint |

---

## 23. Immediate first patches

The highest-value first pull requests are:

1. **Schema/authority PR**
   - add V2 records and service;
   - add immutable hypothesis/evidence rows;
   - make MCP consume the canonical API;
   - add malformed/integrity failure tests.

2. **Historical importer/corpus PR**
   - import current bug pages with provenance;
   - label the ZeroKind related-case set;
   - retain uncertain extraction as notes.

3. **Common debug policy PR**
   - add `debug-common` canonical skill;
   - make existing debug/T32/bug-review skills reference it;
   - require prior-case lookup and negative-evidence validation.

4. **Exact retrieval PR**
   - id/error/build/artifact/stack indexes;
   - explainable result;
   - generated “similar cases and refuted hypotheses” view.

5. **Daily-debug correctness PR**
   - RFC 3339/date;
   - full pagination;
   - no cursor advance on failure;
   - source event receipts;
   - split fetch failure from no messages.

These five patches establish safe foundations before automatic artifact download or firmware flashing is expanded.

---

## 24. Reference sources

### Repositories inspected

- Simple: <https://github.com/ormastes/simple>
- SPipe: <https://github.com/ormastes/Spipe>

### Crash capture and build identity

- Zephyr Core Dump: <https://docs.zephyrproject.org/latest/services/debugging/coredump.html>
- Zephyr Logging: <https://docs.zephyrproject.org/latest/services/logging/index.html>
- ESP-IDF Core Dump: <https://docs.espressif.com/projects/esp-idf/en/stable/esp32/api-guides/core_dump.html>
- ESP-IDF configuration reference, including app ELF SHA and binary logging: <https://docs.espressif.com/projects/esp-idf/en/stable/esp32/api-reference/kconfig-reference.html>
- Crashpad overview design: <https://chromium.googlesource.com/crashpad/crashpad/+/HEAD/doc/overview_design.md>
- Breakpad introduction/minidumps: <https://chromium.googlesource.com/breakpad/breakpad/+/master/docs/getting_started_with_breakpad.md>
- GNU linker build ID: <https://sourceware.org/binutils/docs/ld/Options.html>
- ARM CMSIS Event Recorder: <https://arm-software.github.io/CMSIS-View/latest/evr.html>
- ARM CMSIS Event Recorder theory: <https://arm-software.github.io/CMSIS-View/latest/er_theory.html>

### Reproduction and testing

- Git bisect: <https://git-scm.com/docs/git-bisect>
- LLVM libFuzzer: <https://llvm.org/docs/LibFuzzer.html>
- Clang UndefinedBehaviorSanitizer: <https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html>
- Delta Debugging: Andreas Zeller and Ralf Hildebrandt, “Simplifying and Isolating Failure-Inducing Input,” IEEE TSE, 2002.

### Intake

- GitHub issue forms: <https://docs.github.com/en/communities/using-templates-to-encourage-useful-issues-and-pull-requests/syntax-for-issue-forms>
- GitHub webhook events: <https://docs.github.com/en/webhooks/webhook-events-and-payloads>
- Microsoft Graph change notifications: <https://learn.microsoft.com/en-us/graph/api/resources/change-notifications-api-overview>
- Jira webhooks: <https://developer.atlassian.com/cloud/jira/platform/webhooks/>
- MinIO/AIStor client metadata and object commands: <https://docs.min.io/aistor/reference/cli/>

### Retrieval

- Gordon V. Cormack, Charles L. A. Clarke, Stefan Büttcher, “Reciprocal Rank Fusion Outperforms Condorcet and Individual Rank Learning Methods,” SIGIR 2009.
- Nils Reimers and Iryna Gurevych, “Sentence-BERT: Sentence Embeddings using Siamese BERT-Networks,” EMNLP 2019, <https://arxiv.org/abs/1908.10084>.

### Statistics and NAND

- NIST/SEMATECH e-Handbook, control charts: <https://www.itl.nist.gov/div898/handbook/pmc/section3/pmc31.htm>
- NIST/SEMATECH e-Handbook, EWMA: <https://www.itl.nist.gov/div898/handbook/pmc/section3/pmc314.htm>
- Yu Cai et al., “Experimental Characterization, Optimization, and Recovery of Data Retention Errors in MLC NAND Flash Memory,” <https://arxiv.org/abs/1805.02819>
- Yu Cai et al., “Read Disturb Errors in MLC NAND Flash Memory,” <https://arxiv.org/abs/1805.03283>
- Jürgen Freudenberger et al., “Read Reference Calibration and Tracking for Non-Volatile Flash Memories,” Electronics 2021.
- IBM Research, “Characterization and Analysis of Bit Errors in 3D TLC NAND Flash Memory,” IRPS 2019.
- IBM Research, “Open Block Characterization and Read Voltage Calibration of 3D QLC NAND Flash,” IRPS 2020.

---

## 25. Final design rule

The central rule is:

> **A bug is a chain of identity-bound observations, hypotheses, experiments, and verification claims—not a mutable conclusion.**

SPipe should make the cheapest correct next check easy, make repeated disproven work difficult, and make every local or remote result reusable without confusing similarity with causality.
