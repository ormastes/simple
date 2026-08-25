# SPipe Knowledge Compiler Operator Guide

**Status:** Design guide; commands become operational as implementation waves land  
**Date:** 2026-08-25

## 1. What the knowledge compiler does

The SPipe Knowledge Compiler turns canonical project documents, source
metadata, and tests into a stable artifact graph, searchable indexes, and
read-only virtual documentation views. Canonical content stays single-copy and
is identified by immutable artifact and section UIDs. Physical and virtual
paths are locations, not identities.

SPipe remains usable without Simple. Its dependency-free JavaScript provider
is the baseline; a configured Simple provider may add faster search, compiler
symbols, duplication analysis, and database integration without changing the
observable identity, ranking, trace, or projection contracts.

## 2. Audience

This guide is for repository operators, document authors, reviewers, LLM
agents, and administrators who need to index project knowledge, browse it from
different viewpoints, recover traceability, safely rename or move artifacts,
or review tree and common-knowledge proposals.

It is not an implementation API reference. Architecture and provider details
belong in `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md` and
`doc/05_design/infra/spipe/spipe_knowledge_compiler.md`.

## 3. Safety model

- Canonical files are writable only through their normal authoring workflow or
  an approved SPipe refactor transaction.
- `spipe://` resources, editor virtual filesystems, and `.spipe/view/` are
  generated read-only projections.
- Artifact and section UIDs never change or get reused. Keys, headings, tags,
  and paths may change while retaining aliases.
- Inferred trace edges are proposals. Strict profiles accept only accepted
  explicit or generated evidence.
- Physical reorganization and common-knowledge publication always require
  review and explicit approval.
- Remote embeddings are disabled unless project policy explicitly permits the
  content and provider.
- Never capture credentials, authorization headers, private artifact bodies,
  or remote-provider secrets in evidence.

## 4. Preconditions

Before operating on a workspace:

1. use the repository-managed SPipe command and self-hosted Simple binary where
   configured;
2. confirm the project registry, linked-project revisions, trust scopes, and
   worktree identity;
3. keep unrelated dirty files and other-agent work outside the operation;
4. ensure `.spipecache/` and `.spipe/view/` are derived/ignored locations;
5. use explicit temporary roots for destructive fault or recovery exercises;
6. run `spipe doctor` to resolve incomplete links, interrupted transactions, or
   incompatible indexes before applying a mutation.

An unavailable optional provider is not a reason to abandon core operation.
The compiler should report degraded capabilities and continue with the
dependency-free exact/BM25/graph path. Do not describe that as proof of the
missing provider.

## 5. Primary operator workflow

### 5.1 Index canonical knowledge artifacts

Build a first snapshot for a new workspace:

```text
spipe index build
spipe index status
```

For an existing indexed workspace, apply only changed inputs:

```text
spipe index update
```

The result should identify the workspace, project revision, worktree overlay,
schema/parser/analyzer versions, indexed artifact count, graph delta, lexical
delta, diagnostics, and snapshot identity. A no-change update must be
deterministic and must not rewrite unchanged derived objects.

Resolve duplicate UIDs and ambiguous keys before relying on search or trace
results. A direct filesystem move may be recovered by UID, exact content hash,
or Git rename evidence; ambiguous similarity recovery requires review.

### 5.2 Browse virtual knowledge views

List a virtual directory and read an artifact or generated directory index:

```text
spipe view list spipe://workspace/<workspace>/view/feature/search/
spipe view read spipe://project/<project>/artifact/<uid>
```

Supported projections include lifecycle, feature, component, layer, matrix,
trace, project, status, and diagnostics. Large directories paginate; ordering
and collision suffixes are deterministic. A virtual file must resolve to one
canonical UID and display its canonical path.

For file-only agents:

```text
spipe view materialize feature
```

Browse `.spipe/view/`, but never edit it. Regeneration replaces derived
representations and uses content hashes to avoid rewriting unchanged files.

MCP clients follow this sequence:

1. start/connect to the configured server;
2. send `initialize`;
3. send `notifications/initialized` and request `tools/list`;
4. call `spipe_list` or `spipe_read`;
5. verify a representative tool-level error, such as a rejected traversal or
   write attempt.

Legacy stdio remains a compatibility transport. MCP 2026 stateless requests
use deterministic pagination and visibility-safe cache hints. Private or
authorization-sensitive results must never enter a public cache scope.
Resource URIs, cursors, query hashes, and cache entries bind the immutable
snapshot, principal/policy version, filters, and analyzer version. HTTP mode
must use an explicit safe bind, authentication, origin policy, and bounded
request/rate/parser/query budgets; it does not inherit trust from loopback.

### 5.3 Search and trace artifacts

Resolve exact identity before guessing a path:

```text
spipe resolve <uid|key|alias|path>
spipe search <query> --project <project> --feature <feature>
spipe trace show <artifact>
spipe trace matrix <scope>
spipe trace check --profile strict
```

Search explanations identify exact/alias matches, BM25 field matches, graph
distance, optional semantic rank, RRF contributions, boosts, and penalties.
Exact identity and stable tie-breaking remain deterministic across providers.

Trace output distinguishes edge type, origin, status, confidence, provenance,
revision, and evidence. Candidate edges from lexical, structural, semantic, or
LLM inference remain proposals until accepted. A strict trace check must not
count them as compliance evidence.

If a result is stale, inspect whether its source, specification, provider,
analyzer, or linked-project revision changed. Reindex the affected delta and
rerun the trace check; do not delete the stale diagnostic without new evidence.

### 5.4 Apply a transactional refactor

Always preview a mutation:

```text
spipe refactor plan doc rename <artifact> <new-key-or-title>
spipe refactor plan doc move <artifact> <new-path>
spipe refactor plan section rename <section> <new-heading>
spipe refactor plan tag rename <old> <new>
```

Review resolved UIDs, content-hash preconditions, affected paths/references,
aliases, trace effects, linked projects, worktree identity, and rollback map.
Apply only the approved transaction token:

```text
spipe refactor apply <transaction>
```

The compiler journals before writes, stages atomic edits/moves, updates aliases
and canonical locations, reparses/reindexes the delta, verifies links and
accepted traces, and commits only a valid new state. A stale hash or changed
worktree must fail before mutation. Approval tokens are snapshot-bound,
single-use, and expiry-limited. Durable before-images, deterministic lock
ordering, file and parent-directory sync, and an explicit fail-closed
cross-device policy are required; multi-file atomicity must not be overstated.

On interruption or failed verification:

```text
spipe doctor
spipe refactor rollback <transaction>
```

Recovery must yield either the complete old state or complete new state. Keep
the journal, hashes, diagnostics, and rollback receipt until independent review
confirms content, graph, aliases, and paths agree.

### 5.5 Audit tree balance and promotion candidates

Audit organization without moving canonical content:

```text
spipe tree audit <scope>
spipe tree suggest <scope>
```

A proposal explains depth, fanout, file-count, semantic entropy, trace-chain
splits, cohesion, move/churn cost, public paths, constraints, old/new objective,
confidence, aliases, and rollback. Virtual projections may regenerate when
hard constraints hold. Physical changes require explicit approval:

```text
spipe tree apply <proposal>
```

For reusable knowledge:

```text
spipe knowledge scan <projects...>
spipe knowledge candidates
spipe knowledge promote <candidate> --scope family
```

Review source projects/revisions, exact and fingerprint evidence, lexical and
structural similarity, graph role, optional semantic evidence, conflicts,
trust/visibility, license/secret findings, proposed generalized wording,
provenance, and consuming-project validation. Publication to family/common
scope is never automatic.
Prefer `extends` plus a local override when a project constraint must survive.

## 6. Diagnostics and expected operator response

| Diagnostic family | Meaning | Response |
|---|---|---|
| `SPK001`/`SPK002` | duplicate UID or ambiguous key/alias | stop; resolve identity before indexing further |
| `SPK101`–`SPK103` | broken artifact/section/cross-project reference | restore target, correct revision, or apply reviewed refactor |
| `SPK201`–`SPK205` | missing or stale trace evidence | add accepted evidence or leave the gate failing |
| `SPK301`/`SPK302` | missing/conflicting classification | review metadata; do not let inference silently decide |
| `SPK401` | virtual path collision | inspect deterministic UID suffix and ambiguity |
| `SPK501` | promotion candidate | review provenance/conflicts; not a completion claim |
| `SPK601`–`SPK603` | tree threshold finding | review proposal; no automatic physical move |

Existing `TRC231` and `TRC232` mirrored SSpec/manual diagnostics remain
compatibility checks. Their path relationship is a projection; stable IDs are
the authoritative identity.

## 7. Security and privacy checks

Reject `..`, encoded traversal, absolute-path injection, cross-root escape,
unauthorized project/revision access, and symlink/junction escape before file,
graph, index, or cache effects. Resolve the physical target before authorization
and apply deny-by-default visibility/capability policy. Security-sensitive
opens must resist symlink time-of-check/time-of-use replacement rather than
authorizing one path and opening another.

Cache entries include project, revision, worktree/snapshot, parser/schema,
analyzer/provider, and visibility identity. Authorization-sensitive results
must use private scope. Remote semantic providers require explicit policy and a
content classification compatible with that provider.

Server-backed search must preserve snapshot consistency, query budgets,
cancellation, field/collection capabilities, per-tenant cache isolation, and
commit-before-ack durability. Enumeration or a schema listing is not evidence
that those controls ran.

Provider commands are configured trusted code, not document-controlled input.
Resolve them from an administrator-approved registry, do not interpolate
artifact text into a shell command, bound their CPU/memory/output/lifetime, and
treat provider output as untrusted structured data.

### Configured hostile-input limits

MCP limits are: 1 MiB frame, 32 KiB headers, JSON depth 64, 128-byte method,
8 KiB URI, 4 KiB query, 256 KiB decoded string, 512 KiB aggregate arguments,
100 list entries, 1,000 candidates, trace depth 8/2,000 nodes, 1 MiB response,
200 generated lines/about 6,000 model tokens, and 16 in-flight requests.

Provider query limits add: 128 tokens, 64 Boolean clauses, nesting depth 8,
32 terms/phrase and 64 phrase terms total, 256 expansions, 32 filters with 64
values each, 1,000 hits, 128 explanation terms and 32 fields per hit, 64 KiB
explanation per hit/512 KiB per page, 1,000 delta documents, 64 fields/document,
1 MiB field value, 1,000 duplicate candidates total/100 per document, 1,000
symbols, and a client deadline from 50 ms through 30 s. Regex and leading
unbounded wildcards are unsupported.

At limit-plus-one, expect typed `frame_too_large`, `limit_exceeded`,
`deadline_exceeded`, or `invalid_request`; stale/cross-scope requests return
`stale_cursor` or `unauthorized`. Transactions and analysis additionally use
`precondition_failed`, `transaction_conflict`, `recovery_required`,
`unsupported_version`, `constraint_conflict`, `budget_exceeded`,
`provider_unavailable`, and `incompatible_contract`. Rejection occurs before
dispatch, protected allocation, cache publication, filesystem mutation, prompt
interpretation, promotion, or generated-skill output.

## 8. Performance and scale operation

Measure rather than infer startup or query behavior. Retain fixture identity,
revision, command, provider/version, cold/warm state, repetitions, percentile
method, elapsed time, max RSS, index size, candidate count, and exit status.

The research evaluation targets are 50,000 artifacts, 1,000,000 graph nodes,
ten linked projects, five worktrees, warm query P95 below 100 ms, and one-file
update P95 below 100 ms. All absolute latency figures are provisional until
Wave 0 records and qualifies the host, corpus, command, warmup, repetitions,
percentile method, variance, and max RSS; they are not current PASS thresholds.

Hot request paths must not rescan the full tree, reread unchanged files, or
spawn repeated provider processes. Production wrappers execute cached compiled
artifacts. MCP stdio waits indefinitely while idle; an idle server is not a
timeout failure. Bound request execution, payloads, pagination, graph
traversal, and query budgets separately.

## 9. Verification commands

Five compile-valid executable design scaffolds and five exact-path authored
mirrors now exist. The scaffolds deliberately fail with `DESIGN-SCAFFOLD`; the
mirrors explicitly identify themselves as non-generated and non-PASS. After
production oracles replace the fail-fast helpers, use the exact inventory in
`doc/03_plan/sys_test/spipe_knowledge_compiler.md`. Run, documentize, and scan
each changed spec once after it is ready:

```bash
bin/simple test test/03_system/app/spipe/feature/<name>_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/spipe/feature/<name>_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/app/spipe/feature/<name>_spec.spl
find doc/06_spec -name '*_spec.spl' | wc -l
```

The last command must print `0`. Provider-native acceptance additionally uses
`SIMPLE_NO_STUB_FALLBACK=1` and native mode. Changes to Simple MCP/LSP owners
also run their focused check, stdio integration, and native smoke gates from
the system-test plan.

Generated manuals must report complete with `0 stubs`, retain authored scope
and limitations, show the applicable frozen workflow steps, include complete
folded executable source, and pass independent operator-readability review.

## 10. Troubleshooting

### Search results differ between providers

Confirm corpus, analyzer, field weights, fixed-point scorer version, snapshot,
and document-ID tie-breaking. Run the golden parity fixture. Do not normalize a
provider mismatch with an arbitrary score tolerance when ordering is required.

### A virtual artifact is missing or duplicated

Resolve its UID, inspect classifications and collision suffix, compare the
canonical snapshot with the worktree overlay, and check the linked-project
revision. Rebuild only when incremental parity is in doubt; repeated full
rebuilds are not normal recovery.

### A strict trace gate rejects a plausible link

Inspect its origin and status. A high-confidence inferred edge is still a
candidate. Accept it only after reviewing source evidence, edge direction,
revision, and the requirement/test authority.

### Refactor apply stops midway

Do not manually complete half the moves. Run `spipe doctor`, inspect the
transaction journal and hash preconditions, then recover or roll back the named
transaction. Preserve the receipt for review.

### Rebalancer repeatedly proposes moves

Confirm stable cluster UIDs, snapshot identity, hysteresis, cooldown,
minimum-improvement gate, and recent-move penalty. Unchanged input must produce
no churn. Leave physical content in place until the defect is resolved.

### Semantic or server provider is unavailable

Record the degraded capability and continue with exact/BM25/graph retrieval if
policy permits. Do not claim semantic, server, WAND, or authorization evidence
from fallback execution.

## 11. Compatibility and deferred surfaces

Existing SPipe CLI, setup, link, and `doctor` behavior remains compatible.
Legacy MCP stdio and MCP 2026 stateless transports share a protocol-neutral
knowledge core. MCP tools/resources, materialized views, and an editor virtual
filesystem are the supported exposure order.

FUSE/ProjFS is deferred until client evidence proves those mechanisms
insufficient. An absent OS mount is therefore not a core failure, and no
materialized or editor view may be misreported as OS-mount evidence.

## 12. Related knowledge

- `doc/00_llm_process/feature_expert/modern_sspec/skill.md`
- `doc/00_llm_process/feature_expert/mcp_runtime/skill.md`
- `doc/00_llm_process/feature_expert/link_manager/skill.md`
- `doc/00_llm_process/feature_expert/cache_identity/skill.md`
- `doc/00_llm_process/layer_expert/test_runner/skill.md`
- `doc/00_llm_process/layer_expert/infra_storage/skill.md`
- `doc/00_llm_process/layer_expert/server_transport_security/skill.md`

When the feature behavior becomes reachable, add/update the dedicated feature
expert entry and link these adjacent experts to the canonical guide rather than
duplicating the full contract.
