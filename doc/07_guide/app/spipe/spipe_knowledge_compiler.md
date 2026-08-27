# SPipe Knowledge Compiler Operator Guide

**Status:** Waves 1–3 accepted; sealed read-only projection and metadata-lexical slices admitted; authority service is contract-only; Wave 4 partial; Waves 5–11 otherwise planned
**Date:** 2026-08-27

## 0. Current capability and evidence matrix

This table is authoritative for deciding whether a workflow below is runnable.
Commands described for an unlanded wave are contract previews, not executable
operator instructions.

| Capability | State | Evidence / operator consequence |
|---|---|---|
| Legacy CLI/MCP modularization | Accepted (Wave 1) | Commit `185f3303282`; existing host, fine-tune, doctor, and legacy MCP surfaces remain the only released command surface. |
| Identity, parsing, registry, snapshots, overlays | Accepted (Wave 2) | Commit `deccbce964e`; callable through the dependency-free JavaScript library and tests, not through the planned Knowledge Compiler CLI. |
| Typed graph and diagnostics foundation | Accepted (Wave 3) | Commit `5e2a049eb89`; graph publication and diagnostic APIs are library surfaces. Later lifecycle/run/result trace nodes remain Wave 7. |
| Checked common BM25 scorer | Accepted foundation | Commit `2b9f25f8604`; this does not prove SPipe search, RRF, provider, JavaScript fallback, or DBFS parity. |
| Dependency-free raw RRF kernel | Accepted foundation | Commit `595ba6e449`; deterministic fusion only, without identity dominance, graph candidate construction, post-fusion adjustments, or an exposed search command. |
| Authority-bound bounded reranker | Accepted foundation | Commit `44e65a6713`; page-local fixed-policy adjustments with verified raw/evidence digests, but no exposed search command or proof of global candidate-pool completeness. |
| Complete-pool RRF v2 | Accepted foundation | Commit `32574ab884`; up to 3,000 declared complete, digest-bound internal candidates are reranked before the 1,000-hit public cap. Producer/search receipt binding and exposed orchestration remain open. |
| Authority-bound exact identity | Accepted foundation | Commit `d1b601697f`; canonical UID/key/active-alias resolution over a receipt-bound authorized projection. Retrieval, graph traversal, fusion orchestration, and exposed search remain open. |
| Pair-based reranker evidence v3 | Accepted foundation | Commit `f89b120be7`; ordered accepted-edge/receipt pairs preserve shared-receipt authority losslessly. Graph candidate generation and exposed search remain open. |
| Projection Kernel V1 | Accepted narrow slice | Commit `6b7fc8b83f6`; strict `spipe://` URI parsing plus deterministic list/read over a caller-authorized immutable inventory. Its unsigned cursor is only a local continuation; it is a pure library, not MCP, a read-authorizer, a materializer, or a canonical-write path. |
| SnapshotLexicalSearchV1 | Accepted narrow slice | Commit `6b7fc8b83f6`; fixed-point lexical discovery over sealed identifier, title, and classification metadata. Its logical root binds workspace, snapshot, authorization-scope digest, and metadata-index root; it is not full-text search or a provider bridge. |
| Transactional AuthorityServiceV1 | Selected contract; backend deferred | Commits `a134cb516f6` and `9655bd6fa0f` freeze the sole-mutable-owner, trust/composition, response-receipt, and fail-closed-client rules. No admitted durable quorum store, authenticated service runtime, canonical publish/open, availability, durability, linearizability, RPO/RTO, or F2 backend exists. |
| Trace kernel | Frozen, unadmitted candidate | The candidate failed duplicate-reference validation at its review cap. It is not graph/trace admission evidence and must not be resumed by copying its source. |
| Wave 4 provider/search integration | In progress | JSON, Unicode/analyzer, provider, DBFS, and parity candidates are rejected, blocked, or unverified unless a later accepted commit says otherwise. |
| Virtual views/MCP 2026/refactor/rebalance/promotion/skill compiler/DB adapters | Planned | Waves 5–11; the corresponding commands in this guide are unavailable. |
| Five system SSpecs and manuals | RED design scaffolds | Their fail-fast helpers are intentional. They are not runtime or release evidence. |

To inspect the released surface, use the installed package's `spipe --help`
and MCP `tools/list`; never infer command availability from a planned syntax
block. A missing admitted self-hosted Simple runtime does not block standalone
JavaScript work, but it does block native Simple admission. Rust bootstrap-seed
or raw-source execution is not substitute evidence.

## 1. What the knowledge compiler does

The target SPipe Knowledge Compiler turns canonical project documents, source
metadata, and tests into a stable artifact graph, searchable indexes, and
read-only virtual documentation views. The released Waves 2–3 currently cover
identity, parsing, immutable snapshots/overlays, typed graph publication, and
diagnostics as JavaScript library APIs.  No operator/CLI/MCP search or virtual
view surface is released; the two narrow read-only library kernels below are
admitted. Canonical content stays single-copy and paths are not identities.

SPipe remains usable without Simple. The target architecture requires a
dependency-free JavaScript search provider. Today the dependency-free baseline
also includes the narrow metadata lexical and immutable projection kernels, but
not full-text/provider search, persistence, or an operator surface. A later
configured Simple provider may add faster search, compiler symbols, duplication
analysis, and database integration without changing observable contracts.

### 1.1 Admitted read-only kernels

The two admitted slices have deliberately small boundaries. A trusted caller
must already have selected an immutable inventory and authorization scope;
neither slice opens a snapshot, authenticates a caller, or determines what the
caller may see.

- `ProjectionKernelV1` accepts a deeply frozen inventory and a fixed workspace
  plus authorization-scope hash. It parses only canonical `spipe://` URIs and
  lists lifecycle, feature, component, layer, project, and status projections.
  Pages are deterministically ordered and bounded to 100 entries. Their
  unsigned base64url local continuation carries and equality-checks workspace,
  snapshot, scope, view, path, page limit, and last key, but callers can alter
  `after`; signing/integrity and authorization belong to a deferred adapter. A
  read returns generated Markdown identifying one canonical artifact; `write()`
  always rejects.
- `SnapshotLexicalSearchV1` accepts only frozen metadata for UID, key, aliases,
  title, kind, status, feature, component, layer, and project. It uses the
  checked fixed-point lexical index to search identifier, title, and
  classification fields. Its returned `logical_root` incorporates exactly the
  workspace UID, snapshot UID, authorization-scope digest, contract, and
  metadata-index root for caller-side binding/verification. It is not an
  authorization/authenticity receipt, and an individual hit must not be treated
  independently as scoped proof.

They do **not** provide MCP exposure, read authorization, materialization,
full-text bodies, provider bridging, persistence or incremental indexing,
trace/matrix views, authority publish/open, or a durable backend. The target
CLI and MCP examples elsewhere in this guide remain future contracts unless a
later accepted capability matrix entry says otherwise.

The next authority prerequisite is also not implemented by either kernel: a
sealed, mutually authenticated local-IPC composition must construct the
authority client and response verifier from trusted OS peer credentials or a
platform certificate facility. Every definitive terminal/winner response and
every negative `NoAdmissionV1` proof must arrive in a signed receipt bound to
wire header/version, response kind, service-instance UID, authority key
ID/epoch, tenant UID, authenticated caller-subject digest, connection-binding
digest, scope digest, request digest, idempotency key-or-null, issue/expiry,
and the applicable outcome fields. A terminal/winner binds
exact durable terminal and decision bytes/digests and forbids a negative proof;
`NoAdmissionV1` instead binds the same request tuple plus a quorum watermark
and signed immutable negative-index proof and forbids a terminal/winner. Until
that composition and verifier are admitted, no operator may treat a transport
result as canonical publish/open authority.

### 1.2 Authority service: selected design, no released backend

`AuthorityServiceV1` is the selected F1/N1 authority model.  Its eventual
durable decision store, not a client-side current pointer, chooses the winner
for `publish`, `resolveAccepted`, and canonical `open`.  A client invokes the
existing P2 commit-input selection once per publish attempt, sends its exact
replay-envelope digest, and has no local success, filesystem, lock, CAS,
backend-selection, or retry-publish path.  A pre-admission failure is
`ServiceTransportFailureV1` or `CapabilityDeniedV1`; a post-admission lost
reply is client-local `IndeterminateDeliveryV1` and is resolved only by the
same scoped key and request digest.  `NoAdmissionV1` requires a durable quorum
watermark and signed negative-index proof.

This is an architecture/contract decision only.  Until a separately reviewed
durable store and mutually authenticated service composition are admitted,
canonical publish/open is unavailable and normal Node fails closed before a
mutable decision.  F2/N2 may be used only inside the service after live,
private certification of the pinned backend tuple; it is never a Node fallback.
Offline search remains independent of this unavailable authority service.

## 2. Audience

This guide is for repository operators, document authors, reviewers, LLM
agents, and administrators who need to index project knowledge, browse it from
different viewpoints, recover traceability, safely rename or move artifacts,
or review tree and common-knowledge proposals.

It is not an implementation API reference. Architecture and provider details
belong in `doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md` and
`doc/05_design/infra/spipe/spipe_knowledge_compiler.md`.

## 3. Target safety invariants

The following invariants govern future mutation, view, search, and promotion
surfaces; their presence here does not mean those surfaces are released:

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

For currently released host/package operations:

1. use the repository-managed SPipe package;
2. pass the host root explicitly when SPipe is not mounted at `.spipe/spipe`;
3. keep unrelated dirty files and other-agent work outside the operation; and
4. use `spipe doctor /absolute/host/root` only for package/host link checks.

Index, transaction, provider, cache, and materialized-view preconditions apply
only after their implementation waves land. Current `doctor` does not inspect
them, and there is no released exact/BM25/graph fallback search path.

### 4.1 Standalone install and released-surface discovery

SPipe has no baseline npm dependencies. From the Simple repository root, use
the package directly:

```sh
cd examples/05_stdlib/spipe
node cli/spipe.js --version       # 0.1.0
node cli/spipe.js --help
npm run check
npm test
npm run build                    # invokes sh scripts/build.shs
```

For a local global command installation, run
`npm install -g ./examples/05_stdlib/spipe` from the repository root. This
installs `spipe` and `spipe-mcp`. `spipe doctor /absolute/host/root` requires
an explicit host root when the package is not mounted at `.spipe/spipe`; SPipe
does not search upward from the current directory.

The released MCP server is newline-delimited stdio:

```sh
node mcp/server.js
```

Its initialize response currently advertises protocol `2024-11-05`, server
`spipe` version `0.1.0`, and tools/resources capabilities. `tools/list` returns
exactly `spipe_info`, `spipe_experts`, `spipe_read_doc`,
`spipe_fine_tune_guide`, `spipe_fine_tune_model_guide`, and
`spipe_fine_tune_template`; `resources/list` returns only `spipe://skill`.
There are no resource templates, list-change notifications, cache hints,
Knowledge Compiler tools, or MCP 2026 HTTP transport yet.

## 5. Primary operator workflow

### 5.0 Current Waves 2–3 API boundary

The dependency-free package now provides schemas and JavaScript APIs for
artifact/project/section/edge/alias/view records, Markdown/SDN/SSpec/source
metadata parsing, identity diagnostics, UID-injection planning, explicit
workspace/project/worktree registration, immutable objects and snapshots, and
per-worktree overlays. `compileKnowledgeInventory` accepts an explicit bounded
set of `{path, content}` inputs; filesystem enumeration remains a workspace
adapter responsibility so the core cannot silently scan or escape a project
root.

Wave 2 validates explicit artifact, section, scenario, and source-symbol IDs by
record kind. Parser budgets apply across the full inventory, including metadata
and recursively nested inline SDN. Unmarked sections remain typed candidates
with explicit incremental deltas rather than masquerading as canonical section
records.

Trust is registry-derived. The raw compatibility compiler always emits
`untrusted_data`; elevated compilation requires a composition-root-injected,
verification-only `AuthorizationPort` and an Ed25519 receipt bound to the exact
project, worktree, revision, canonical source set, policy version/hash,
capability, principal, expiry, and audit evidence. `reviewed_reference` requires
`trust_scope.assign`; `executable_policy` requires `policy.publish`. Content,
plain option objects, forged signatures, provisional artifacts, stale receipts,
and receipts for a different source set cannot elevate trust.

Linked-project resolution authorizes the requested relation UID before relation
lookup or any project, revision, trust, mount, or filesystem disclosure.
Unauthorized callers receive the same bounded diagnostic shape for existing and
missing relation IDs. Persisted registries additionally bind the trusted
workspace root, authorized project roots, and exact realpath-resolved mount.

Unmarked artifacts receive only snapshot-scoped provisional identity of the
form `P-<project-uid>-<content-hash>`. A durable UID proposal is opaque random
identity and is persisted only through a later approved canonical edit; it is
never derived from path, title, key, or content. Tests may inject a deterministic
UID factory solely to replay a transaction fixture.

The `spipe index`, `view`, `search`, `trace`, and refactor commands below are
the stable planned operator surface. They must not be treated as reachable
until their named implementation wave and focused compatibility evidence land.

#### 5.0.1 Executable Waves 2–3 library walkthrough

The following is the current standalone Knowledge Compiler entry point. Run it
from `examples/05_stdlib/spipe`; it performs no repository scan or canonical
write:

```sh
node --input-type=module <<'NODE'
import assert from "node:assert/strict";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  compileKnowledgeInventory,
  compileKnowledgeDelta
} from "./src/core/knowledge_compiler.js";
import { parseMarkdownArtifact } from "./src/parser/index.js";
import { planUidInjection } from "./src/core/identity.js";
import { WorktreeOverlayStore } from "./src/storage/overlay_store.js";
import { ZERO_HASH } from "./src/storage/canonical.js";

const context = {
  project_uid: "P-000000000000000000000000000000AA",
  worktree_uid: "W-000000000000000000000000000000BB",
  revision_id: "185f330328248b89813baf9229b14781f53a60c4",
  overlay_generation_hash: ZERO_HASH,
  policy_hash: "4".repeat(64)
};
const original = `<!-- spipe:artifact uid=A-00000000000000000000000000000001 key=design.search.core aliases=[old.search] -->
# Search Core

## Stable identity
<!-- spipe:section uid=S-00000000000000000000000000000001 key=design.search.identity -->
Paths are locations.
`;

const inventory = compileKnowledgeInventory({
  ...context,
  inputs: [{ path: "doc/search.md", content: original }]
});
assert.match(inventory.snapshot.snapshot_uid, /^spks1-[0-9a-f]{64}$/);
assert.equal(inventory.identity.resolve("old.search").status, "resolved");
assert.equal(Object.isFrozen(inventory), true);

const changed = original.replace("Paths are locations.", "Paths remain locations.");
const incremental = compileKnowledgeDelta(inventory, [{
  operation: "upsert", path: "doc/search.md", content: changed
}]);
assert.equal(incremental.delta.artifacts.updated.length, 1);
assert.equal(incremental.delta.artifacts.updated[0].uid,
  "A-00000000000000000000000000000001");

const cacheRoot = mkdtempSync(join(tmpdir(), "spkc-overlay-"));
try {
  const overlay = new WorktreeOverlayStore({
    cacheRoot, worktreeUid: context.worktree_uid
  });
  overlay.set("doc/search.md", changed);
  const reloaded = new WorktreeOverlayStore({
    cacheRoot, worktreeUid: context.worktree_uid
  });
  assert.equal(reloaded.read("doc/search.md").toString(), changed);
} finally {
  rmSync(cacheRoot, { recursive: true, force: true });
}

const unmarked = parseMarkdownArtifact(
  "# New Note\n\n## Missing identity\nBody.\n",
  { path: "doc/new-note.md", projectUid: context.project_uid,
    revision: context.revision_id }
);
let sequence = 0;
const proposals = planUidInjection(unmarked, {
  uidFactory: prefix => `${prefix}-${String(++sequence).padStart(32, "0")}`
});
assert.ok(proposals.some(({ kind }) => kind === "artifact_uid"));
assert.ok(proposals.some(({ kind }) => kind === "section_uid"));
assert.ok(proposals.every(({ canonical_mutation }) => canonical_mutation === false));
console.log("wave2_walkthrough=pass", inventory.snapshot.snapshot_uid,
  incremental.inventory.snapshot.snapshot_uid);
NODE
```

Expected result is one `wave2_walkthrough=pass` line and no assertion failure.
`planUidInjection` is dry-run-only: no UID apply/persist API, marker-write
authorization receipt, or `RefactorService` is released. Trust elevation is a
separate composition-root operation through `createAuthorizationPort` and a
verified signed receipt; see `test/integration/knowledge_wave2_test.js` for the
accepted fixture.

#### 5.0.2 Admitted projection and metadata-lexical test commands

These are the only current executable commands for the new read-only kernels;
they exercise library contracts rather than an operator CLI, server, or mount.
Run them from `examples/05_stdlib/spipe`:

```sh
npm run test:projection-kernel
node --test test/unit/snapshot_lexical_search_test.js
```

`test/unit/projection_kernel_test.js` covers canonical URI rejection,
deterministic collision-safe and cursor-bound listing, canonical artifact
rendering, read-only rejection, and immutable-input enforcement.
`test/unit/snapshot_lexical_search_test.js` covers metadata-only deterministic
lexical search, frozen/closed input and snapshot binding, bounded non-cursor
requests, and the absence of authority, filesystem, process, environment,
network, or provider imports. These tests do not qualify release availability,
MCP behavior, authorization, durable authority, full-text retrieval, or native
provider conformance.

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

This is a target operator workflow, not a current CLI/MCP instruction. The
admitted `ProjectionKernelV1` supplies only the pure URI/list/read kernel
behind a future caller-authorized adapter; it does not expose these commands.

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

This is a target workflow. The admitted `SnapshotLexicalSearchV1` is a
metadata-only library and does not expose `spipe search`, resolve, trace, or
matrix commands.

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
symbols, and a client deadline from 1 through 30,000 milliseconds inclusive.
The deadline starts when the decoder accepts the first frame-header byte, so
ingress, decoding, validation, normalization, hashing, execution, and response
construction consume one semantic budget. Regex and leading unbounded
wildcards are unsupported.

At a frame-size limit-plus-one, expect a payload-free local
`TransportDiagnosticV1(code:frame_too_large)` and silent close, not a provider
response. Invalid UTF-8 is handled identically with `code:invalid_utf8`.
These two classes are never bound `ProviderErrorV1` codes. After a complete
typed request is host-bound, applicable named operations may return bound
`limit_exceeded`, `deadline_exceeded`, or `invalid_request` errors;
stale/cross-scope requests return
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

Qualified Wave 4 evidence is collected only through
`examples/05_stdlib/spipe/test/perf/measure_qualified_search.mjs` with explicit absolute
`SPIPE_SIMPLE_BIN` and `SPIPE_STAGE4_PROVENANCE` paths plus explicit profile,
fixture, operation-plan, functional-receipt, and output arguments. Its sole
helper contract is
`measureQualifiedSearch(profile_path, fixture_path, operation_plan_path,
functional_receipt_uri, output_path)`; there are no overloads or implicit
counts. The collector admits the binary with the same
Stage 4 verifier as provider conformance and writes a closed
`spipe-qualified-search-receipt-v1`; failure writes no receipt. The receipt
binds binary/provenance/profile/fixture/query-plan hashes and counts; closed
compiler/toolchain and collector-runtime identities, versions, and hashes; the
canonical functional-conformance receipt URI/hash; and the canonical
`benchmark_operation_plan_v1.json` path/hash. That operation plan fixes every
discarded warmup and measured round: verify/reset baseline `S0`, run all queries
in plan order before mutation, alternate publish-then-rebuild and
rebuild-then-publish order across rounds with an `S0` reset between them, and
verify declared `S0`/`S1` hashes without restarting the provider. The receipt
then carries one warm startup sample, raw query/update/rebuild samples,
recomputable nearest-rank P95, process-tree peak RSS, and no-spawn/no-scan
counters.

The functional prerequisite is exactly one closed canonical-JSON object:

```text
schema = "spipe-functional-conformance-receipt-v1"
subject = {implementation, provider_id, provider_version,
           protocol_version, analyzer_id, score_id}
executable = {canonical_path, sha256, stage4_provenance_sha256}
fixture = {id, sha256, snapshot_sha256, query_plan_sha256}
scope = {principal_scope_digest, policy_version}
matrix = [{id, status = "passed", evidence_sha256}]
result = {status = "passed", checker_id, checker_version,
          checker_sha256, completed_at_utc}
```

Every leaf except `matrix` is a nonempty UTF-8 string; every SHA-256 and scope
digest is exactly 64 lowercase hexadecimal characters. `matrix` contains each
required `W4-SRCH-01` through `W4-SRCH-08` and `W4-SRCH-10` through
`W4-SRCH-14` ID exactly once in ascending numeric order, with no other ID; it
explicitly excludes performance cell `W4-SRCH-09`. Ordering is acyclic:
functional conformance produces this receipt first, then qualified performance
consumes it and alone evaluates `W4-SRCH-09`; cell 09 is never a prerequisite
of the receipt it consumes. The checker requires byte-equal subject, executable,
fixture, and scope bindings to the benchmark inputs. Unknown, missing, null,
duplicate-normalized, wrong-typed, failed, duplicate, or out-of-order fields or
entries are `NOT EVIDENCE`.

The operation plan is exactly one closed canonical-JSON object:

```text
schema = "benchmark-operation-plan-v1"
plan_id = nonempty ASCII identifier
fixture = {id, sha256, query_plan_sha256}
counts = {warmup_count, sample_count, query_count_per_sample}
states = {s0_snapshot_sha256, s1_snapshot_sha256}
delta = {artifact_id, delta_sha256, before_revision,
         before_content_sha256, after_revision, after_content_sha256}
reset = {method = "restore-canonical-s0-v1", expected_snapshot_sha256}
queries = [{query_index, query_id, canonical_request_sha256,
            expected_result_sha256}]
warmup_rounds = [{round_index, operations}]
measured_rounds = [{round_index, operations}]
```

Counts and indices are non-negative JSON safe integers; counts are positive.
Digests are 64 lowercase hexadecimal characters and all other leaves are
nonempty UTF-8 strings. Query indices are contiguous from zero and array order
is execution order. Each `operations` array uses only `verify_s0`,
`query_all`, `publish_delta`, `reset_s0`, `rebuild_s0`, and `verify_s1`.
Warmup rounds encode the fixed discarded schedule; measured even and odd rounds
encode the two required alternating schedules, with `query_all` before either
mutation and an ending `reset_s0`. The arrays have exactly the declared counts,
their indices are contiguous, and their query cardinality equals
`query_count_per_sample`. `reset.expected_snapshot_sha256` equals
`states.s0_snapshot_sha256`; the delta's before/after bindings produce exactly
S0/S1. Canonicalization is `canonical-json-v1`: UTF-8 without BOM or trailing
LF, NFC strings, unsigned decimal safe integers, lexicographically sorted NFC
object keys, and preserved array order. Unknown, missing, null,
duplicate-normalized, wrong-typed, inconsistent, or noncanonical input is
`NOT EVIDENCE`; its SHA-256 covers those exact canonical bytes.

Those counters are not provider telemetry. A profile-approved platform adapter
must create sealed process containment and begin observation before provider
launch, retain every descendant through exit and reparenting, and write a
sequence-numbered, SHA-256-chained event journal. The checker independently
replays its bound URI/hash to recompute membership, lifecycle, query-window
spawns, warm workspace enumerations, repeated unchanged-source reads, and peak
RSS. Missing/lost events, a broken chain, late attachment, an untracked
descendant, or a platform without that fail-closed adapter is `NOT EVIDENCE`.
A missing admitted
binary is `NOT EVIDENCE`, so the Rust seed, source execution, or an informal
`time` transcript cannot satisfy W4-SRCH-09.

The checked-in `spipe-qualified-search-profile-v1` is authoritative for the
exact subject, host/kernel/architecture/CPU and core policy, approved counter
adapter, fixture, warmup/sample method, integer MAD variance limit, and
latency/RSS/index/cache budgets. The collector observes those values rather
than copying them. Samples cannot be discarded or retried; host, adapter, or
variance mismatch is `NOT EVIDENCE`.

Every timed query binds its duration to expected and observed SHA-256 digests
of the canonical result and status `matched`; a fast wrong result invalidates
the receipt. The ratio is `floor(rebuild_median_ns * 1000 /
publish_median_ns)` with checked integers; zero is invalid and `20.0` means
`>= 20000`.

Counter evidence is canonical UTF-8 JSONL with an opened-root path identity,
contiguous sequence and predecessor chain, kernel-level process/filesystem
events, explicit loss reporting, and a terminal membership/hash record. Loss,
overflow, ambiguous identity, surviving descendants, or chain failure is
`NOT EVIDENCE`; provider logs and textual path matching are insufficient.

Every closed event additionally contains `source_version`,
`source_content_sha256`, and `source_change_witness = {kind,
identity_generation, size_bytes, modified_time_ns, witness_sha256}`. For
`source_open` and `source_change` events, `source_version` is a non-negative safe
integer and `source_content_sha256` is exactly 64 lowercase hexadecimal
characters. Non-source events use `source_version = 0`,
`source_content_sha256 = ""`, and the typed zero/empty-string witness sentinel.
A successful `source_open` must carry the current per-path-identity
version, the hash of the exact bytes read, and a witness derived by the approved
adapter from the opened handle; a `source_change` event is added to the event
enum and must increment that identity's version and bind the new content hash
and witness before a later open is attributed. Replay classifies a reread as
unchanged only when path identity, version, content hash, and witness all match
and no intervening `source_change` exists. Missing, regressing, skipped, or
contradictory versions, hashes, or witnesses are `NOT EVIDENCE`, making an
unchanged-source reread mechanically replayable rather than inferred from path.

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

This is a future provider runbook. After the fallback/provider wave lands,
record the degraded capability and continue with the explicitly negotiated
available sources if policy permits. Today there is no released search fallback.
Never claim semantic, server, WAND, or authorization evidence from degradation.

## 11. Compatibility and deferred surfaces

Existing SPipe CLI, setup, link, and `doctor` behavior remains compatible.
Legacy MCP stdio is the only released transport. The protocol-neutral core,
MCP 2026 stateless HTTP transport, Knowledge Compiler tools/resources,
materialized views, and editor virtual filesystem are target/deferred surfaces
in that implementation order.

FUSE/ProjFS is deferred until client evidence proves those mechanisms
insufficient. An absent OS mount is therefore not a core failure, and no
materialized or editor view may be misreported as OS-mount evidence.

## 12. Related knowledge

- `doc/04_architecture/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
- `doc/05_design/infra/spipe/spipe_knowledge_compiler_search_providers.md`

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

## 13. Current Wave 4 search evidence

The checked canonical BM25 slice is accepted at commit `2b9f25f8604`, limited
to `src/lib/common/search/ranking.spl` and
`test/01_unit/lib/common/search/ranking_spec.spl`. Highest-capability review is
`PASS`; a clean integration checkout produced source check `PASS` and focused
specification `PASS 30/30`. The runtime was bootstrap-seed/non-Stage-4, so do
not present these receipts as Stage 4 runtime qualification or as Wave 4
completion.

Do not use the rejected standalone DBFS `wave4_compatibility` bundle. It
duplicates scoring instead of delegating to the canonical scorer, has weak
probe coverage, lacks executed clean/parity and embeddings-zero-use evidence,
and violates capability/statistics contracts. Its status is
`FAIL`/`NOT-EVIDENCE`, and none of its files is accepted.

The next DBFS implementation must be a real facade over the canonical scorer.
Acceptance requires idempotent remove/re-add statistics, query-term
deduplication, `explain:false` until explanations are implemented, and an
independent final-corpus clean rebuild oracle. Wave 4 remains `IN PROGRESS`.

### 13.0.1 W4A operator admission rule

The detailed W4A closure sequence is Section 13.1 of
`doc/05_design/infra/spipe/spipe_knowledge_compiler_search_providers.md`.
Operators must treat the JS, native-Simple, and DBFS probes as fixture inputs,
not admission evidence.  A target becomes usable only when its closed
`ProviderConformanceRecordV1` verifies the pinned manifest, logical root,
scope binding, statistics, score/explanation/page digests, and applicable
matrix cells.  Native process use additionally requires the framed-transport
security matrix and binary/Stage-4 provenance; a qualified performance receipt
is separately required for NFR performance claims.  PureDatabase, textual DB,
and server DB adapters are Wave 10 consumers of the frozen contract and must
not be implied by DBFS or provider success.

The clean post-push lint attempt stopped before a lint verdict because the
bootstrap runtime/codegen path could not resolve `Array.sort_by`. Record that
as a tooling blocker, not a scorer failure or pass. No duplicate-check receipt
exists for this slice.

### 13.1 Rejected DBFS facade attempt

Do not consume the current clean-clone DBFS candidate. Its exact scope was the
four files
`src/lib/nogc_sync_mut/db/dbfs_engine/fts/{__init__,bm25,inverted_index,search}.spl`
plus
`test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl`.
All three bounded cycles executed zero owned-code assertions. Stage 3 Simple
`9ce412a1d102de421de6d7042d8dc5c65201cc514b463b9b6a5bc5de2f66970c`
lacks `check`/`test`; Rust seed
`c9c783b8568cf9a199945fe1ee98d08615b728387e6c89cbdc9b50e600f3e091`
stopped on unrelated `nogc_async_mut/path.spl` `E1002 unsafe` and
`plan_sdn.spl` `Dedent`.

Highest-capability static review is `FAIL`, admissible files `[]`. The
candidate mutates nested value-semantic state without complete copy/writeback,
commits lexical state before trigram/content state, mismatches the frozen
`contains_document` `me fn` ABI, and lacks the full statistics, clean-rebuild,
contains/absent, ordering, legacy-success, and checked-upsert failure oracle.

The facade direction and focused fixture are useful design input, not accepted
implementation. Rebuild child state and write it back once, make the whole
engine update atomic, correct the ABI, complete the oracle, and use a capable
pure-Simple runtime for the next fresh bounded run. Wave 4 remains
`IN PROGRESS`.

### 13.2 Analyzer V1 handoff

Do not accept the current analyzer candidate: static status is `FAIL`,
admissible files `[]`, because it is unbounded and its parity claim is false.
The analyzer lane owns only `src/lib/common/search/analyzer.spl` and
`test/01_unit/lib/common/search/analyzer_contract_spec.spl`;
`src/lib/common/search/__init__.spl` is merge-owned. The generated UCD17
tables and manifest are missing from `main` and must land first.

The common batch ABI consists of
`SearchFieldIdentityV1(Identifier|Title|Heading|Classification|Body)`,
`AnalyzerErrorV1(InvalidLimits|InvalidFieldIdentity|InputLimitExceeded|
InvalidUtf8|NormalizedLimitExceeded|TokenBytesLimitExceeded|
TokenCountLimitExceeded|DistinctTermLimitExceeded)`,
`AnalyzerIdentityV1` with eleven text fields
`analyzer_id,unicode_version,unicode_manifest_sha256,normalization_id,
lowercase_id,tokenizer_id,stop_words_id,stop_words_sha256,stemming_id,
field_schema_id,limits_schema_id`, and `AnalyzerLimitsV1` with five i64
fields `max_input_bytes,max_normalized_bytes,max_token_bytes,max_tokens,
max_distinct_terms`.

Result types are `AnalyzedTokenV1(value:text,position:i64,
exact_identifier:bool)`,
`AnalyzedTextV1(normalized:text,tokens:[AnalyzedTokenV1])`,
`AnalyzedQueryTermV1(value:text,qtf:i64)`, and
`AnalyzedQueryV1(normalized:text,terms:[AnalyzedQueryTermV1])`. Call
`analyze_field_v1(text,SearchFieldIdentityV1,AnalyzerIdentityV1,
AnalyzerLimitsV1)->Result<AnalyzedTextV1,AnalyzerErrorV1>`,
`analyze_query_v1(text,AnalyzerIdentityV1,AnalyzerLimitsV1)
->Result<AnalyzedQueryV1,AnalyzerErrorV1>`, or
`unsigned_utf8_less(text,text)->bool`.

Semantics are UCD17 NFC -> default lowercase, not folding -> NFC; maximal
`Alphabetic|Decimal_Number|Mark|_` tokens; pre-stopword one-based positions;
`[a,an,and,of,the,to]` with SHA-256
`6f0a7c26d3d0e3d06a2fbbbeaa1843294f83c3be26baf1c04651191e011510bf`;
identifier full-normalized/no-trim append-last token at position zero with
deduplication; and QTF terms sorted by unsigned UTF-8.

Use query limits `4096/4096/4096/128/128` in struct order. Field input
hard-caps at 1,048,576 bytes and configured `max_tokens` at 524,288. Unicode
manifest, stopword, limits, and schema identities are cache identity. Analyzer
code must not embed, spawn a process, access a network, or use locale state.

This batch layer feeds but does not replace `ProviderAnalyzerLimitsV1`,
`ProviderAnalyzedTokenV1`, `ProviderAnalyzedTokenSinkPort`, or
`ProviderStreamingAnalyzerV1`; adapter parity is required. Wave 4 remains
`IN PROGRESS`.

### 13.3 Rejected Unicode 17 prerequisite bundle

The Unicode prerequisite is atomic across 14 files: generator, license, seven
UCD inputs (`UnicodeData`, `DerivedCoreProperties`, `PropList`,
`SpecialCasing`, `CaseFolding`, `CompositionExclusions`,
`NormalizationTest`), generated JavaScript/Simple tables, manifest, and the
JavaScript/Simple tests. These live under
`examples/05_stdlib/spipe/tools/unicode/`,
`examples/05_stdlib/spipe/src/search/generated/`,
`src/lib/common/search/generated/`,
`examples/05_stdlib/spipe/test/fixture/wave4_search/`,
`examples/05_stdlib/spipe/test/unit/unicode_17_tables_test.js`, and
`test/01_unit/lib/common/search/unicode_17_0_0_spec.spl`.

The 256-CCC bounded-linear normalization repair, O(n) sigma contexts, and
4,096-element JavaScript chunking are useful but unaccepted. JavaScript passed
7/7 for 20,034 records in five NFC forms, every scalar, and 1 MiB. Cycle 2's
Rust-seed Simple attempt timed out `124` without a summary; cycle 3 repeated
the JavaScript PASS and supplies no additional evidence.

Highest-capability status is `FAIL`, admissible `[]`. Remaining defects are
unproved Simple push/value semantics and optimizer bounds, direct
`rt_file_read_text` use rather than the file facade, orphan
`REQ-SPK-SEARCH-UNICODE-001`, the wrong generated-JavaScript license path,
and weak independent `Case_Ignorable` final-sigma lowercase coverage.

Accept none of the bundle. Repair the static defects first, then run complete
parity once on a capable pure-Simple runtime. The analyzer prerequisite is
still missing and Wave 4 remains `IN PROGRESS`.

### 13.4 Admitted authority-bound lexical source

Commit `9eb667e23b` is the accepted lexical-source checkpoint. Its focused suite
passed `16/16`; the package passed `158/158` unit, Wave 2 `9/9`, Wave 3 `25/25`,
Wave 4 `9/9`, legacy, security, workflow, and performance gates; final
highest-capability review passed. This evidence covers the dependency-free
producer only, not a provider adapter or an integrated `spipe search` command.

The producer owns four synchronous boundaries:

| Port | Operational meaning |
|---|---|
| `verifySearchReceipt` | Attest the exact snapshot/scope/policy/query/source binding before provider access |
| `readLexicalProviderPage` | Return one frozen, digest- and receipt-bound provider page |
| `authorizeArtifactCandidate` | Recheck every collected artifact exactly once without early exit |
| `verifyLexicalEvidence` | Attest the complete page-set and ordered-rank evidence exactly once |

For troubleshooting pagination, verify the chain rather than inspecting only
the visible candidates: the first page has a null inbound cursor digest; each
later page's inbound digest equals the previous page's next-cursor digest; ranks
remain dense; page receipt, page digest, requested limit, exact exclusion, and
provider identity do not drift; and no cursor, receipt, or artifact repeats.
Only an exhausted or `sourceK`-complete chain produces a lexical RRF source.

Digest fixtures must use restricted `spipe-canonical-json-v1`: NFC strings and
keys, unsigned UTF-8 normalized-key order, dense arrays/closed records, safe
integers excluding `-0`, and lowercase long C0 escapes. In particular U+0009
is `\u0009`; a short `\t` spelling produces a different preimage and is not
valid evidence. Use an independent canonicalizer for parity tests.

If exact identity is pinned, pass it as `excludedDocumentUid` to the provider.
The provider must exclude it before ranking and pagination and bind it in every
page and receipt. Do not fetch 1,000 then filter locally: that leaves at most
999 candidates and falsely labels an incomplete source as `sourceK=1000`.

Provider integration remains gated on an explicit ownership/interface freeze
and conformance oracle. The adapter must prove
`spipe-search-provider/1.0`, `spipe-unicode-lex-v1`, `bm25-fixed-v1`, stable
implementation identity, pre-ranking exclusion, cursor continuity, page
receipts, and aggregate evidence. No adapter filename is canonical yet.

The graph candidate under `/tmp/spkc-graph-candidates-4OKnKd` is not reusable
evidence: cycle-cap result `13/14`, with an uncontracted cyclic
`workUnits <= 9` assertion; seven static repairs but no full package or final
review; no commit. Keep graph boost and AC-4 open.

Continue only through these owned pairs:

1. `src/search/graph_candidates.js` +
   `test/unit/search_graph_candidates_test.js`;
2. the separately frozen provider adapter/protocol + conformance oracle;
3. `src/search/rerank_evidence.js` +
   `test/unit/search_rerank_evidence_test.js`;
4. `src/search/pipeline.js` + `test/unit/search_pipeline_test.js`.

All relative paths in this list are under `examples/05_stdlib/spipe/`. The
pipeline order is exact identity pin, provider-owned exclusion, complete
lexical/graph sources, complete-pool RRF-v2, standalone evidence verification,
pair-based reranking, then user limit. A green standalone lexical test is not an
integrated-search or AC-4 completion signal.

### 13.5 Admitted graph source and frozen lexical-provider boundary

The previous `/tmp/spkc-graph-candidates-4OKnKd` result remains a useful failed
attempt record, but do not use its `13/14` status as the current graph status.
The corrected product/oracle pair is admitted at commit `626b3e0797` with
focused `16/16`, full unit `174/174`, Wave 2 `9/9`, Wave 3 `25/25`, Wave 4
`9/9`, legacy integration, performance, and pre-runtime/final
highest-capability review all passing. Its cyclic fixture requires the exact
counter `workUnits == 10`.

The graph source is safe to consume only through its public factory. Its main
operator-visible guarantees are:

- depth is capped at 3; `sourceK` at 1,000; page work at 50,000; total work at
  500,000; snapshot nodes at 20,000; edges at 50,000; roots at 1,001;
- every node is authorized before accepted-edge receipt verification;
- traversal is both-direction, deterministic, and can re-expand descendants
  after a better same-distance path arrives;
- cursors are opaque, factory-local, single-use, and call no authority port on
  continuation;
- total-work exhaustion destroys the continuation and returns no candidates;
- evidence keeps ordered edge/receipt pairs, so two edges sharing one receipt
  do not lose their path multiplicity;
- the edge-set, evidence, source-identity, and candidate digests have independent
  literal goldens.

This admits graph candidate generation, not integrated search. AC-4 remains
open.

#### Provider version and operation

Use wire `{major:1,minor:1}` and require capability
`authorized_lexical_page:true` before issuing `lexical_page`. Do not rename the
semantic identities: provider remains `spipe-search-provider/1.0`, analyzer
`spipe-unicode-lex-v1`, and score contract `bm25-fixed-v1`. The page and adapter
identities are `spipe-authorized-lexical-provider-page-v1` and
`spipe-authorized-lexical-provider-adapter-v1`. A protocol 1.0 provider is
legacy-compatible, but it is not conforming for the admitted lexical source.

Send:

```text
{binding_digest,query_text,query_digest,excluded_document_uid,
 requested_limit,cursor}
```

Expect:

```text
{logical_root,excluded_document_uid,exclusion_applied,requested_limit,
 page_start_rank,hits,next_cursor,exhausted}
```

Each hit is `{document_id,source_rank,score_milli}`. When an exact artifact is
pinned, confirm that its UID was removed before scoring/top-k insertion and
pagination. Snapshot `N`, `df`, and average document length must not change;
exclusion is a result-pool rule, not a corpus mutation.

#### Cursor and receipt troubleshooting

A cursor binds provider generation/implementation, workspace, snapshot,
authorization scope, logical root, binding/query digests, exclusion, and next
rank. It intentionally does not bind the current `requestedLimit` or `qr-*`
receipt. A smaller terminal page is normal; drift in any stable binding is not.

Treat receipt namespaces separately:

| Receipt | Owner | Meaning |
|---|---|---|
| `qr-*` | Simple wire provider | One transport query/page response |
| `D-*` | Adapter-side evidence authority | Signed lexical-page evidence consumed by `lexical_source.js` |

The adapter-side authority must verify `qr-*`, persist the signed `D-*` receipt,
and return exactly the nine page-receipt fields: receipt UID, `lexical_page`
kind, binding digest,
excluded UID, exclusion decision, inbound cursor digest, requested limit,
next-cursor digest, and page digest. Never pass `qr-*` where a `D-*` UID is
required or synthesize authority from the visible wire payload. The separate
aggregate evidence authority resolves the retained `D-*` receipts.

#### Implementation and current limits

The current authorized implementation slice is JavaScript/in-process. Its
owners are `src/index/{contracts,logical_index}.js` and
`src/provider/{protocol,adapter,js_fixed_point,index,lexical_page}.js` under
`examples/05_stdlib/spipe/`; its oracle and vector fixture are
`test/unit/search_lexical_provider_page_test.js` and
`test/fixture/wave4_search/authorized_lexical_provider_page_vectors.json`.
The mapped Simple-native owners are
`src/app/spipe_knowledge_provider/{lexical,wire_query,wire_core,protocol,service}.spl`.

Do not attach a long-lived Simple process to the current synchronous
`readLexicalProviderPage` port by blocking, polling, retry-sleeping, or spawning
per page. Native process support waits for a reviewed async lexical-source v2
or async collection plus immutable synchronous replay design. No process
adapter filename is canonical yet.

Operational candidate targets are lazy startup, no hot process spawn/full-tree
scan/retry sleep, startup P95 at most 250 ms, and warm lexical P95 below 100 ms
on 50,000 artifacts. Maximum RSS needs a qualified receipt and configured cap;
its numeric target is blocked on Wave 0 profiling. These are targets, not
current provider-conformance evidence.

The standalone rerank-evidence implementation is currently active. After it
and the provider adapter are independently admitted, the pipeline order is:
exact resolution; excluded complete lexical collection; graph generation;
complete-pool RRF v2; authority-bound rerank evidence; pair-based reranking and
explanations; user limit last. Until the end-to-end pipeline passes, keep AC-4
open.

#### Full authority bridge: authoritative operator contract

The preceding nine-field receipt description is only the projection consumed
by `lexical_source.js`. A bridge that creates that projection without a full
signed record is the rejected pre-authority design. The admitted implementation
target is the synchronous in-process
`createAuthorizedLexicalProviderPageBridgeV1` factory. It captures exactly:

```text
{providerSession,issueTransportQueryReceiptV1,
 verifyTransportQueryReceiptV1,executeLexicalPageV11,
 lexicalEvidenceAuthority,lexicalEvidenceStore,clockNowMs}
```

and exposes only the frozen
`{readLexicalProviderPage,verifyLexicalEvidence}` pair. Every call is direct;
a Promise/thenable, process spawn, poll, retry sleep, or per-page file read is a
contract failure. `executeLexicalPageV11` receives the complete wire 1.1
request envelope and returns the complete wire response—not an invented page
projection.

The provider-side companion is
`createInProcessLexicalPageExecutorV11({provider,providerSession,
verifyTransportQueryReceiptV1,lexicalCursorAuthority,clockNowMs})`; it returns
the frozen `executeLexicalPageV11(envelope)` function. Provider-side `qr-*`
checking lives there, while the bridge checks the echoed receipt independently.

Check identity in two layers:

| Layer | Required identity |
|---|---|
| Search semantics | provider `spipe-search-provider/1.0`, analyzer `spipe-unicode-lex-v1`, scorer `bm25-fixed-v1` |
| Transport | `{major:1,minor:1}`, `authorized_lexical_page:true`, `lexical_page` |
| Adapter/page | `spipe-authorized-lexical-provider-adapter-v1`, `spipe-authorized-lexical-provider-page-v1` |
| Evidence | `spipe-lexical-page-evidence-receipt-v1`, `spipe-lexical-aggregate-evidence-receipt-v1` |

Do not diagnose protocol 1.1 as provider semantic version 1.1. Protocol 1.0 is
legacy-compatible but cannot supply authority-bound pages.

Initialization never silently changes minors. A 1.0 request returns the current
closed 1.0 capability record unchanged. A 1.1 request must return 1.1 and the
same closed record plus final `authorized_lexical_page:true`; absent/false is
not conforming. All semantic identity arrays, limits, and `optional_fields:[]`
remain unchanged. Unknown versions or extra fields fail closed.

For each fresh page the observable order is: validate closed structure, scalar
values, negotiated capability, and fixed caps; derive deterministic
session/input/operation/request identity from the raw bounded cursor text;
atomically reserve; then make the bridge start-clock observation and perform
cursor identity/decode/verification/binding/liveness; issue `qr-*`; provider
verification and execution; exact canonical-byte receipt echo; independent
bridge verification; provider page validation; full page `D-*` signature;
atomic store; immediate resolve/re-verification; then projection. No clock,
authority, or cursor authentication operation is permitted before reservation.
The page operation key is `lpo-<64 lowercase hex>` and its request ID is
`req-lp-<the same 64 hex>`. An aggregate operation uses
`lao-<64 lowercase hex>`.
Immediately before success return, the bridge observes the clock again and
rejects/tombstones work that crossed receipt expiry.

A non-null page cursor is strict unpadded Base64Url of the closed signed
`spipe-authorized-lexical-cursor-v1` record. It binds authority/revocation,
adapter and provider implementation/generation/session, workspace/snapshot/
scope/root, lexical binding/query/exclusion, next rank, policy, and expiry. It
intentionally omits `requested_limit` and page-local `qr-*`. A noncanonical
encoding, wrong signature, wrong session, or stale time is `stale_cursor`.
Its cursor authority has the exact `identity/sign/verify` Ed25519 capability
shape and must match the provider session's transport key, authority,
authority/revocation generations, and policy. Evidence receipts may use a
separate signer, but not a different policy.

The full `qr-*` is the existing closed `spipe-query-receipt-v1`, binding
request, operation, provider generation, workspace, snapshot, scope, lexical
root, query hash, policy, authority/revocation generation, issue/expiry time,
key, and signature. The provider checks it before ranking; the bridge checks
the complete echoed canonical bytes after ranking. A partial field echo does
not pass.
Its ID spelling is exactly `qr-` plus 64 lowercase hexadecimal characters.

The stored page `D-*` contains the full provider session and lexical binding,
the complete verified `qr-*`, raw inbound/next cursors, provider identity,
ordered candidates, page digest, authority/key/policy/revocation generations,
issue/expiry, UID, and signature. The returned nine fields are derived from
that record. The aggregate verifier resolves every page `D-*`, verifies the
store digest, UID, signature, embedded `qr-*`, expiry/revocation, root/scope/
policy, page projection, cursor chain, and rank sequence, then recomputes page
set, rank evidence, and output document digests. Only then may it sign/store/
re-resolve the aggregate `D-*` returned as `authorityReceiptUid`.

Authority receipt preimages use restricted canonical JSON framed as
`domain + NUL + U64BE(byte length) + canonical bytes`. Relevant domains are:

```text
SPKC-LEXICAL-PAGE-OPERATION-V1
SPKC-LEXICAL-PROVIDER-SESSION-V1
SPKC-QUERY-PAYLOAD-V1
SPKC-QUERY-RECEIPT-V1
SPKC-AUTHORIZED-LEXICAL-CURSOR-V1
SPKC-LEXICAL-TRANSPORT-RECEIPT-DIGEST-V1
SPKC-LEXICAL-PAGE-EVIDENCE-RECEIPT-V1
SPKC-LEXICAL-OUTPUT-DOCUMENTS-V1
SPKC-LEXICAL-AGGREGATE-OPERATION-V1
SPKC-LEXICAL-AGGREGATE-EVIDENCE-RECEIPT-V1
SPKC-LEXICAL-EVIDENCE-STORE-RECORD-V1
```

The admitted lowercase lexical page/page-set/rank digests keep their existing
unframed convention; a changed golden there is a bug, not a migration.

Replay is exact and bounded. A live operation key resolves and fully
re-verifies the same stored receipt and returns it without calling the
transport issuer, provider executor, evidence signer, or store commit. A
different record under the same key is `operation_conflict`. Expired, revoked, wrong-root, wrong-policy,
or wrong-generation evidence is tombstoned through `tombstoneOperationV1` and
cannot be refreshed in that bridge generation. The first store is process-local
only: all reserved, active/replay, and tombstoned operations share one 4,096
entry cap and 64-MiB accounted canonical-byte cap, including a fixed token
charge and exactly 2,048 bytes of worst-case tombstone headroom pre-charged for
each reservation. Commit replaces that headroom only if the active record fits,
so mandatory cleanup remains possible after a capacity failure. Page records
are capped at 1 MiB and aggregate records at 2 MiB.
Entries are not evicted or overwritten until the bridge generation is
destroyed. Restart persistence is not claimed.

The store surface is exactly
`{reserveOperationV1,commitReceiptV1,resolveReceiptV1,tombstoneOperationV1}`.
After reservation, every failure before commit tombstones the key—including a
failure after `qr-*` issuance—so an identical retry cannot issue a second
receipt. A process crash discards the process-local bridge/provider generation;
recovery requires a new generation and verified search binding.
Store kinds are only `lexical_page` and `lexical_aggregate`. Tombstone reasons
are `expired`, `revoked`, `binding_mismatch`,
`authority_generation_changed`, `policy_changed`, `record_corrupt`, or the
catch-all `interrupted`. The `inputDigest` is exactly the corresponding page or
aggregate operation digest; it is never caller-selected metadata.

If trusted cursor-authority `identity`, `sign`, or `verify` malfunctions after
reservation, persist the catch-all `interrupted` tombstone before returning
public `internal_error`. Do not add `internal_error` to the tombstone enum or
persist the public code as a reason. A specific expiry, revocation, binding,
authority-generation, policy, or record-corruption classification established
first retains precedence.

Successful page and aggregate bridge calls observe the trusted clock at start
and again immediately before return. The provider executor independently does
the same around receipt verification and ranking. End observations must show
every receipt, cursor, and evidence record still live and authority-current; a
call that finishes after expiry is tombstoned and rejected.

Failure triage should follow the fixed order: invalid shape; exceeded bound;
protocol/contract mismatch; binding/cursor drift; replay conflict; invalid
`qr-*`; provider unavailable; corrupt page; unverified evidence; internal
error. Public errors remain generic. In particular, `unauthorized` points to
transport receipt verification, while `evidence_unverified` points to `D-*`
authority/store/aggregate verification.

Provider caches own immutable snapshot ranking only. The adapter caches one
validated session. The evidence store owns receipts/replay only. Provider
fallback is chosen before the bridge is created and may not change between
pages; a mid-collection provider failure invalidates the collection.

The complete JavaScript ownership is
`src/index/{contracts,logical_index}.js` and
`src/provider/{protocol,adapter,js_fixed_point,lexical_page,
lexical_evidence_store,index}.js` under `examples/05_stdlib/spipe/`, plus the
independent page unit oracle and Wave 4 authority vectors. Do not route this
through `durable_lifecycle.js`, attach a Simple subprocess, or claim native or
cross-restart durability. Exact schemas/preimages and test requirements are in
detail design Section 17.7. Until those tests and highest-capability review
pass, report the bridge as **contract frozen, not conforming** and keep AC-4
open.

#### Current operator handoff (2026-08-26)

Treat commit `47a922eec6` as a reviewed provider-authority **contract**, not a
provider implementation. The attempt at
`/tmp/spkc-lexical-provider-z15Uhp/repo` ended at the pre-runtime review cap
without an in-scope product or oracle edit. A fresh implementation must follow
the complete ABI above and detail design Section 17.7. Do not resume from the
rejected minimal adapter that only manufactures the visible nine-field
projection.

Do not consume `/tmp/spkc-rerank-evidence4-aIcFIZ/repo` as admitted code. Its
`src/search/rerank_evidence.js` and
`test/unit/search_rerank_evidence_test.js` are untracked, uncommitted candidate
files. Focused `16/16`, full unit `190/190`, Wave 2 `9/9`, Wave 3 `25/25`, Wave
4 `9/9`, legacy, security, workflow, and performance checks are green, but the
third-cycle final highest-capability review still found two blockers: preserve
`limit_exceeded` precedence for oversized derived evidence arrays, and bind the
semantic contract string to the admitted consumer contract. Repair and review
that exact pair in a fresh session; do not rerun unchanged green gates first.

Resume in this order: provider implementation/admission, rerank-evidence
repair/admission, then integrated pipeline. Keep AC-4 open until the final
pipeline oracle passes.

#### Superseding operator handoff (2026-08-26)

Use commit `4455b760da` as the admitted rerank-evidence implementation. Its
single admission run passed syntax, focused `18/18`, unit `192/192`, Wave 2
`9/9`, Wave 3 `25/25`, Wave 4 `9/9`, legacy, security, workflow, and performance
checks; independent xhigh review passed in cycle 2 of 3. Do not resume from the
older `/tmp/spkc-rerank-evidence4-aIcFIZ/repo` candidate and do not rerun those
unchanged green checks.

Do not use the latest provider-authority ABI draft. That lane stopped with
`FAIL` after the mandatory third cycle, without product edits, product tests,
or a repository-history commit. Its four unresolved blockers are
collision-result signaling, executor error classification, cursor error
precedence, and canonical-byte accounting versus heap/RSS limits. Object
`3827a1099e` under `/tmp/spkc-provider-abi-repair2-clean` is retained only for
forensic comparison; its contract text is not an operator contract.

Resume with a fresh provider-ABI repair, obtain independent admission, then
implement and admit the provider. The integrated pipeline remains waiting on
that provider. Keep Wave 4 and AC-4 open.

#### Cursor-authority failure operator handoff (2026-08-26)

The final-four representation blocker is contractually resolved. After a
reservation, an unclassified trusted cursor-authority malfunction must first
persist legal tombstone reason `interrupted` and then return public
`internal_error`. Never add `internal_error` to the tombstone enum. Preserve
the earlier specific-failure precedence. Provider implementation, tests, and
admission are still pending; keep Wave 4, AC-4, and the integrated pipeline
open.

#### Full ABI consolidation operator handoff (2026-08-26)

Do not use the eleven-item consolidation draft. It stopped `FAIL` after the
mandatory third review/fix cycle, with no product edit, product test, admitted
contract, or push. Snapshot `e5c556de59d` at
`/tmp/spkc-provider-abi-full-uWb9kD/repo` is immutable forensic material only;
never copy its rejected contract text into an implementation prompt.

Implementation-readiness review passed, but independent highest-capability
review found two self-containment blockers. Section 17.11 excludes Section
17.7.1 while depending on its exact `providerSession`, authority, and executor
schemas. Section 17.11 also excludes Section 17.7.9 while lacking the complete
public error record/field shapes and exhaustive precedence. Start a fresh
bounded session and restate those definitions inside Section 17.11; do not
inherit excluded control prose. Keep provider readiness/implementation/
admission, Wave 4, AC-4, and the integrated pipeline open.

#### Self-containment repair operator handoff (2026-08-26)

Do not use the fresh self-containment repair draft. It stopped `FAIL` at the
mandatory third review/fix cycle, without authoritative contract or product
edits, product tests, or a push. Snapshot
`e77cb713d5703d864f32d16ab3abab0afb5d3215` at
`/tmp/spkc-provider-self-contained-JdUR6t/repo` is immutable forensic material
only; never copy its rejected clauses into an implementation prompt.

Implementation-readiness review passed, but independent highest-capability
review found three exact blockers: overlapping generic code-only unauthorized
and provenance arms, contradictory reserve ordering around binding/cursor
checks and `Cidentity`/`Cverify`, and no exact `requestedLimit` range despite
the candidate cap. In a fresh bounded session, make the executor-error union
structurally disjoint, freeze one reserve/cursor order and tombstone owner, and
state `requestedLimit` as `1..1000`. Keep provider readiness/implementation/
admission, Wave 4, AC-4, and the integrated pipeline open.

#### Three-blocker ABI repair operator guide (2026-08-26)

Treat the provider bridge as the sole evidence-store owner. For any valid page
call, check closed structure, scalar/canonical values, `requestedLimit`
`1..1000`, and byte caps first; reserve next; only then call cursor identity or
verify/decode/binding/liveness logic. A malformed or oversized cursor fails
before reserve; every later cursor failure is mapped by the bridge to the first
applicable existing tombstone reason and is redacted at the public boundary.

The executor may return generic `{code}` only for codes other than
`unauthorized`. Its only unauthorized result carries a private allowed
tombstone reason; persist that reason but return only public `unauthorized`.
Do not copy the reason into a lexical-source result, diagnostic, or MCP reply.
Never let the executor reserve or tombstone. Replay follows the same
post-reservation cursor checks and performs no issuer/provider/sign/commit
work. This remains a contract candidate pending fresh static and independent
review; it does not admit the provider, Wave 4, AC-4, or pipeline.

#### Provider implementation non-admission handoff (2026-08-26)

Do not resume from `/tmp/spkc-provider-admission4-kVaqO2/repo` or copy its
code/contract text. The candidate was based on
`f7ec2dc1b0c0de4b42bb97940b17bec9db29e5a1`, stopped before runtime work after
two immutable xhigh pre-runtime `FAIL` reviews. The final review attempt added
no edit to its exact ten-file scope and ran no runtime test, commit, or push;
the forensic candidate itself has an existing dirty diff.

The bridge contract is presently contradictory: Section 17.14.3 requires
post-reservation cursor identity/decode/verify at the bridge, while the frozen
seven-field bridge factory has no cursor-authority port. Start with a fresh
design session that resolves this configuration ABI. Do not begin implementation
until that decision has fresh implementation-readiness and independent
highest-capability review. Tombstones, exact executor-error discrimination,
full replay verification, cursor digest, store accounting/idempotency,
closed-object accessors, and oracle vectors remain unimplemented. Keep provider
admission, Wave 4, AC-4, and the integrated pipeline open.

## 14. Wave 5 Virtual Knowledge Views: Operator Boundary (2026-08-26)

Virtual knowledge is read from `spipe://workspace/<workspace>/view/...` or
from model-callable `spipe_list`/`spipe_read`/`spipe_search`/`spipe_resolve`/
`spipe_trace`/`spipe_diagnostics`; it is not a writable alternate document
tree. Directory pages are bounded and cursor-paginated. Preserve the supplied
cursor unchanged for the same workspace, authorization scope, and snapshot;
on `stale_cursor`, restart the listing rather than guessing a physical path.

For file-only clients, `.spipe/view/` is generated output. Never edit it. A
single canonical artifact header contains `canonical-uid` and `canonical-path`;
directory, trace, search, and diagnostic pages instead carry a `projection-uid`
and have no canonical edit target. Use a transactional refactor command for
canonical changes once that separate capability is admitted.

Operators configure named workspaces at startup. A request does not infer the
current directory or perform a full scan. Hidden and absent resources return
the same bounded external class; private/mixed results are never placed in a
shared cache. If safe materialization is unavailable on a platform, retain MCP
read-only views and treat the materializer diagnostic as a capability absence,
not permission to use raw filesystem writes.

The first slice remains legacy-stdio compatible and preserves the six existing
tools plus `spipe://skill`. HTTP 2026, subscriptions, editor VFS, and OS mounts
are later adapters and must not be enabled merely because a virtual URI works.

### Wave 5 URI-foundation non-admission (2026-08-26)

The URI-foundation candidate exhausted its three review/fix cycles, is
uncommitted, and is not admitted. Wave 5 URI execution remains pending. Do not
reuse the candidate code.

For a legacy URI such as `spipe://skill`, resolve its canonical target first;
then authorize that canonical target. The receipt must bind normalized alias
URI, canonical URI, workspace/project, target kind/UID, snapshot/revision,
principal-scope hash, policy version, decision, issued/expiry times, and
receipt UID, issuer key ID, revocation epoch, and signature. Before reads
compare fields, `AuthorizationPort` verifies the signed `D-` receipt using its
supported version/key allowlist, canonical `spipe-uri-read-v1\0` payload,
allow decision, live clock window, and current revocation epoch. Reads compare every receipt
field to the direct immutable-snapshot lookup and resolved target; mismatch
reauthorizes or fails closed. URI/query text cannot assert a snapshot, revision,
or target: the service validates existence, ownership, revision, and membership.

`CanonicalReadReceiptV1` has exactly `{receiptVersion, normalizedAliasUri,
canonicalUri, workspaceUid, projectUid, targetKind, targetUid, snapshotUid,
revisionId, principalScopeHash, policyVersion, decision, issuedAtMs, expiresAtMs,
receiptUid, issuerKeyId, revocationEpoch, signature}`.

The fresh admission suite covers workspace roots/views, artifacts, sections,
trace, diagnostics, and legacy aliases (search is a tool input), including
malformed/overlong or unsupported URI; fragment/empty identity, query,
percent/double-decode, traversal/slash/backslash/encoded separator/dot,
drive/UNC/Windows device/reparse/ADS/trailing-dot-space,
Unicode-control/NFC-NFD-collision/mixed-case, cursor,
forged/expired/signature-invalid/revoked/mismatched receipt, and hidden/absent-target
cases. Public failures are bounded and never disclose a canonical path.

The fresh suite also asserts canonical list/read/render success for workspace
root/view, artifacts, sections, trace, diagnostics, legacy aliases after
canonical reauthorization, and `spipe_search`. A successful alias must render
the authorized canonical target rather than echoing an alias-only result.

### 14.1 What must land before an operator can use virtual views (2026-08-27)

No target command in this section is runnable merely because this guide shows
it.  The availability sequence is deliberately strict:

1. The compiler publisher must create the sealed, production authority
   inventory for the exact workspace/worktree/base snapshot/authority snapshot/
   revision tuple (W5A).
2. The branded authorization service must verify canonical read receipts and
   issue/verify durable signed cursor receipts bound to that exact proved target
   and trusted worktree (W5C).
3. The resolver must combine those ports once; MCP resource/tool, legacy stdio,
   HTTP, materialization, and editor adapters must use it rather than opening a
   store or interpreting an unsigned continuation themselves (W5D).

Until all required gates for an adapter pass, use only the admitted library
kernels described in §1.1 and the released MCP compatibility surface in §4.1.
In particular, do not browse a `.spipe/view/` directory that a hand-written
script created, do not copy a cursor between clients or snapshots, and do not
turn a successful local kernel result into an authorization claim.

When the read-only delivery capsule is admitted, operators will have this
behavioral matrix:

| Client | Allowed operation | Important rule |
|---|---|---|
| Legacy MCP stdio | Existing tools plus admitted list/read resource/tool forms | Legacy tools and `spipe://skill` remain compatible; no implicit current-directory workspace. |
| MCP 2026 HTTP | Authenticated resource/tool read | TLS and auth/budget/origin policy run before workspace resolution; bearer values never go in a URL. |
| File-only agent | Browse generated `.spipe/view/` | Manifest-owned read-only output only; user-modified/unknown entries are preserved, not cleaned. |
| Editor VFS | stat/readDirectory/readFile | All write/delete/rename/copy operations reject; canonical changes use a separate refactor plan/apply capability. |

Shared caching is enabled only for a sealed immutable response whose complete
authorized result is public.  Every private, mixed, denied, stale, or
authorization-sensitive result is private/no-store, including conditional
requests; a `304` must never reveal that a hidden resource exists.  If an
adapter is unsupported, it is absent from capability advertisement rather than
emulated by raw paths, a Node filesystem fallback, or a weaker cache policy.
