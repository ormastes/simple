<!-- codex-design -->

# SPipe Knowledge Compiler Search Providers

**Date:** 2026-08-25  
**Status:** Detailed design  
**Scope:** Shared lexical search, SPipe provider protocol, database adapters,
source-symbol export, and reusable duplicate analysis  
**Research:** `doc/01_research/infra/spipe/spipe_knowledge_compiler.md`

## 1. Decision and boundaries

`std.common.search` owns the deterministic lexical scoring contract. Storage,
workspace parsing, database transactions, process transport, and authorization
remain outside that package. SPipe composition wraps either its dependency-free
JavaScript provider or a Simple provider in a `SearchProviderAdapter`;
`KnowledgeCompiler` talks only to internal search ports and never imports or
receives provider implementation details.

The first implementation is exhaustive BM25 over immutable snapshots. WAND,
Block-Max WAND, ANN, and sharding are later execution strategies that must
produce the same ordered top-k result as the exhaustive oracle.

Existing public APIs remain compatibility facades during migration:

- `FtsEngine` and `fts_bm25_*` in DBFS;
- `PureDatabase.search`, `bm25_search`, and `fts5_search`;
- textual database `fts_build`, `fts_search`, and `fts_update` (trigram mode);
- `simple duplicate-check` and MCP `simple_duplicate_check`.

The design does not add search to the database server until capability,
snapshot, durability, cancellation, and bounded-result contracts exist.

## 2. Component ownership

```text
SPipe KnowledgeCompiler
  -> LexicalSearchPort
  -> SemanticSearchPort (optional)
       ^ implemented by
       SearchProviderAdapter
         |- InProcessSearchProviderAdapter
         |    -> JsFixedPointSearchProvider : SearchProvider
         |- ProcessSearchProviderAdapter
         |    -> SimpleProcessSearchProvider : SearchProvider
         |         -> SpipeKnowledgeProvider executable
         |              -> common LexicalSearchPort implementation
         `- ServerSearchProviderAdapter
              -> ServerSearchProvider : SearchProvider

Common lexical implementation (`LexicalSearchPort`)
  <- DBFS adapter
  <- PureDatabase adapter
  <- TextualDatabase BM25 side-index
  <- DatabaseServer SearchCapsule
```

Parent-owned orchestration rules:

- SPipe composition owns `SearchProviderAdapter` selection, health, retry policy,
  and query deadlines. `KnowledgeCompiler` receives only `LexicalSearchPort` and
  optional `SemanticSearchPort`; it never receives, selects, or calls a
  `SearchProvider` directly.
- Each database owns transaction and snapshot boundaries for its index.
- `SpipeKnowledgeProvider` owns request validation and bounded serialization.
- Common search code is pure algorithm/data code and performs no file, process,
  environment, network, or authorization operations.
- Duplicate and symbol services return immutable results; they do not edit
  source or documentation.

### 2.1 Frozen interface vocabulary

These names are normative. Designs and implementations must not introduce
synonymous `*Port`, `*Provider`, `*Service`, or `*Adapter` interface names.

Internal module interfaces:

- `LexicalSearchPort` — index delta, snapshot, lexical query, and explanation;
- `SemanticSearchPort` — optional semantic candidate ranking;
- `SymbolIndexPort` — compiler-owned symbol snapshot and paging;
- `ProjectionPort` — artifact/view projection read operations.

External provider interfaces:

- `SearchProvider` — lexical and optional semantic source-ranking provider;
- `SourceSymbolProvider` — revisioned source-symbol export provider;
- `ProjectionProvider` — virtual projection provider.

Boundary adapter:

- `SearchProviderAdapter` — implements internal `LexicalSearchPort` and optional
  `SemanticSearchPort` while wrapping exactly one external `SearchProvider`.

Concrete adapter names are `InProcessSearchProviderAdapter`,
`ProcessSearchProviderAdapter`, and `ServerSearchProviderAdapter`. They own
translation, validation, deadlines, capability narrowing, cache identity, and
provider lifecycle appropriate to their transport. They are implementations of
the one adapter role, not additional provider or port interfaces.

`JsFixedPointSearchProvider` is the dependency-free JavaScript implementation
of external `SearchProvider`; it is not an additional interface and is always
wrapped by `InProcessSearchProviderAdapter`. The Simple child-process provider
implements `SearchProvider` and is wrapped by `ProcessSearchProviderAdapter`;
server providers are wrapped by `ServerSearchProviderAdapter`. The Simple
symbol surface separately implements `SourceSymbolProvider`.
`SpipeKnowledgeProvider` is the executable/application name, not an interface.

## 3. Common search contract

### 3.1 Target modules

Extend `src/lib/common/search/` with:

```text
analyzer.spl             normalization and tokenization contract
document.spl             document, field, metadata, and revision records
corpus_stats.spl         exact N, df, document length, average length
query.spl                parsed lexical query and filters
top_k.spl                exhaustive oracle and deterministic ordering
provider.spl             capability and index/query ports
explain.spl              term/field contribution records
segment.spl              immutable segment and tombstone model
snapshot.spl             base + delta snapshot identity
fingerprint.spl          normalized hashes, shingles, MinHash/SimHash
similarity.spl           reusable sparse/token/vector comparisons
candidate_bucket.spl     bounded duplicate candidate generation
semantic_provider.spl    optional semantic port, no transport policy
wand.spl                 optional exact WAND execution
block_max_wand.spl       optional exact Block-Max WAND execution
```

Keep `types.spl`, `ranking.spl`, `inverted_index.spl`, and their exports. The
current `InvertedIndex` remains the small append-only positional index; the new
mutable/snapshot index must not weaken its strictly increasing ID invariant.

### 3.2 Logical records

```simple
struct SearchDocument:
    id: text
    revision: text
    fields: [SearchField]
    metadata: [SearchFacet]

struct SearchField:
    name: text
    value: text
    weight_milli: i64

struct SearchFacet:
    name: text
    value: text

struct SearchQuery:
    text_value: text
    filters: [SearchFacet]
    limit: i64
    cursor: text
    explain: bool

struct SearchHit:
    document_id: text
    score: Score
    rank: i64
    explanation: SearchExplanation?
```

Public IDs are text because artifact UIDs and source-symbol UIDs are not
numeric. Storage adapters may assign snapshot-local ordinal `i64` IDs, but must
maintain a bijective ordinal table and use public text IDs for tie-breaking.

### 3.3 Analyzer identity

An `AnalyzerIdentity` contains:

- implementation name and semantic version;
- Unicode normalization and case-fold policy;
- tokenizer version;
- stop-word list hash;
- stemming policy/version;
- field extraction schema version.

Analyzer identity is part of every snapshot and cache key. A mismatch requires
reindexing; a provider must not query an index with a different analyzer.
Initial SPipe policy is Unicode-aware lowercase tokenization without stemming.
Identifiers preserve an additional exact normalized token so `REQ-SEARCH-001`,
artifact keys, aliases, and source symbols cannot be damaged by prose analysis.

### 3.4 Score contract

The normative BM25 implementation is the fixed-point implementation derived
from `src/lib/common/search/ranking.spl`:

- non-negative `ln(1 + (N-df+0.5)/(df+0.5))` IDF;
- `k1 = 1.2`, `b = 0.75`, represented in fixed point;
- exact per-field document length and corpus average;
- one contribution per distinct query term; query term frequency is recorded
  but does not accidentally repeat the same contribution;
- weighted field contributions are accumulated in a wide checked accumulator;
- final score uses `Score` milli units;
- ties use ascending public document ID byte order;
- exact UID/key/accepted-alias matches are handled by SPipe's pre-RRF dominance
  tier, never encoded as IDF or a provider score boost.

The contract has a version (`bm25-fixed-v1`). Providers return it in handshake
and query results. A score-contract mismatch is an incompatibility, not a
warning. Overflow, invalid corpus statistics, or mismatched parallel arrays
return an explicit error.

### 3.5 Deterministic rank fusion

Wave 4 also freezes `rrf-fixed-v1`, an implementable Reciprocal Rank Fusion
contract owned and executed by SPipe. Providers return source-local candidate
rankings only; they cannot return authoritative fused ranks or apply graph,
trace, feature, recency, or lifecycle boosts. SPipe owns graph inputs because
only its accepted typed artifact graph has the required authority. RRF consumes
already ordered candidate lists and never normalizes or compares raw scores.
Initial fusible sources are `lexical`, `graph`, and `semantic`. `semantic` may
be absent. A database server may produce a source ranking but cannot redefine
or execute authoritative fusion.

Exact UID, artifact key, and accepted alias resolution is a dominance tier
before and outside RRF. SPipe resolves it from its identity registry. The two
public operations have distinct mandatory behavior:

- `resolve(value)` returns the one authorized, unambiguous identity match and
  stops. It does not invoke candidate providers, graph ranking, or RRF. No exact
  match returns `not_found`; multiple authorized matches return typed
  `ambiguous_identity`. Unauthorized candidates are neither returned nor
  counted.
- General `search(query)` first performs the same identity lookup. When it
  finds one authorized, unambiguous match, SPipe emits that artifact as final
  rank 1 with `match_tier = exact_identity`, removes its document ID from every
  lexical, graph, and semantic candidate list, and runs RRF only over the
  remaining IDs. Fused results begin at final rank 2. The pinned artifact has no
  RRF rank, contribution, raw score, or adjusted score, so no candidate score
  or boost can tie, outscore, or displace it.

An ambiguous key or alias in general search produces typed identity ambiguity
for the identity tier and does not pin a guessed artifact; policy may then show
ordinary fused discovery results clearly separated from that ambiguity. Stale,
rejected, or unauthorized aliases do not dominate. Exact title/body/token
matches remain ordinary lexical evidence.

For each source, rank is one-based after source-local deterministic tie-breaking
and duplicate document IDs are rejected. Only the first configured `source_k`
candidates (default and maximum 1,000) participate. With default `k = 60`:

```text
rrf_raw(document) = sum over present sources of 1 / (k + source_rank)
```

The implementation uses rational/fixed-point arithmetic defined by the contract,
not binary floating point. Protocol/config accepts `k` in `[1, 10,000]`; its
value, participating ordered source names, `source_k`, and contract version are
part of query/cache identity. Default source order is `lexical, graph,
semantic`; source order affects only explanation rendering, never the sum.

After fusion, only these SPipe-owned bounded deterministic adjustments are
allowed:

```text
accepted-trace proximity boost
same feature/component boost
optional recency boost
stale/deprecated penalty
```

Each adjustment has a named versioned fixed-point cap and the total positive
boost cannot exceed 25% of the maximum possible `rrf_raw` for the participating
sources; total penalties cannot reduce the score below zero. Unaccepted inferred
trace edges cannot contribute the accepted-trace boost. Deployments may disable
adjustments but cannot introduce unnamed boosts without incrementing the fusion
contract version. Final fused ordering is adjusted fused score descending, then
raw RRF score descending, then public document ID ascending. For general search,
this ordering is numbered starting at rank 2 when an exact identity is pinned;
the pinned result is not a member of the fused ordering.

The pinned identity receives an `IdentityExplanation` containing the resolved
UID, matched key/alias, alias authority/status, registry generation, visibility
decision, and `pinned_rank = 1`; it never receives a `FusionExplanation`.
`FusionExplanation` records contract/version, `k`, `source_k`, each source rank (or
absence), its exact fixed-point contribution, every adjustment and cap, raw
sum, adjusted sum, and final tie-break fields. SPipe's implementation has golden
fixtures covering absent sources, different raw-score scales, duplicate IDs,
source-local ties, equal fused scores, capped boosts/penalties,
inferred-versus-accepted trace, and semantic-provider failure.
Golden results compare exact integer contributions, ordered IDs, and explanation
records. SPipe implements identity dominance followed by fusion of lexical and
graph inputs in Wave 4; identity is not an RRF source. Optional semantics and
server integration only add a declared candidate source.

#### 3.5.1 Complete-pool, graph evidence, and cursor contracts

The admitted complete-pool v2 fusion contract accepts declared complete,
counted, digest-bound source lists and returns the entire unique internal pool
up to 3,000. Reranking processes that pool before applying the public 1,000-hit
limit. Source digests prove structural agreement with the declared list; the
search receipt remains responsible for producer authority and completeness.

The graph source is built from an authorization-filtered pinned snapshot. All
declared canonical nodes receive exactly one UID/kind-only authorization recheck
in UID order before any edge is inspected; failures are accumulated through the
fixed call count and collapse to `snapshot_unavailable`. Strict accepted edges
are receipt-verified against the exact snapshot/root/scope/search receipt and
policy. The generator performs both-direction BFS with depth exactly 3;
`sourceK` 1..1000 default 1000; page work 1..50,000 default 50,000;
configurable total work 1..500,000; at most 20,000 nodes, 50,000 edges, and
1001 roots; and 512-byte document IDs. Exact root precedence is
`(seedTier=0,seedRank=0)`; lexical roots use
`(seedTier=1,seedRank=sourceRank)`. Paths repeat
neither nodes nor edges; same-distance improved tuples replace and re-expand a
state. Candidate order is the full architecture tuple followed by artifact UID,
and `sourceK` truncation occurs only after exhaustive bounded traversal.

The continuation is a deeply frozen null-prototype handle with no enumerable
state, branded by its factory and backed by factory-local `WeakMap` state. That
state owns the normalized binding, exact snapshot/digest, frontier, best paths,
counters, and consumed bit. Continuation consumes the old state atomically
before work. Partial output contains only status/version/cursor/counters; total
hard-cap failure destroys state. It is single-use and cannot be serialized,
copied, resumed after restart, or transferred between factories. Bounded state
is GC-eligible when the handle is abandoned. This pure layer has no time
authority, so it makes no TTL claim. Transport/provider cursors remain separate
authenticated wire objects and must not be confused with this local handle.

Graph evidence carries the lossless ordered relation:

```text
accepted_edge_evidence = [
  { edge_uid, authority_receipt_uid },
  ...
]
```

One receipt may authorize multiple edges. Therefore, pair-based evidence—not
two equal-length independently unique arrays—is authoritative. A future
additive reranker evidence contract must accept these pairs and derive display
sets without changing multiplicity or pretending receipts are per-edge.

### 3.6 Index semantics

`LexicalSearchPort` supports:

```text
create(snapshot identity, analyzer identity, score contract)
apply(delta: add | replace | delete)
seal() -> immutable segment
snapshot(base segments, overlay segments, tombstones)
query(snapshot, SearchQuery) -> SearchPage
explain(snapshot, query, document ID) -> SearchExplanation
stats(snapshot) -> SearchIndexStats
```

`replace` is idempotent by `(document ID, revision)`. Repeating the same delta
must not change document count, corpus length, postings, or score. Delete of an
absent ID is a successful no-op. Readers receive one immutable snapshot while a
writer builds the next delta. Segment publication is parent-authoritative and
atomic.

## 4. Provider wire protocol

### 4.1 Transport

The Simple provider is a cached compiled executable at
`src/app/spipe_knowledge_provider/main.spl`.
`ProcessSearchProviderAdapter` starts at most one provider per workspace process
and communicates over stdin/stdout framed messages. `KnowledgeCompiler` neither
starts nor communicates with the process. The adapter must not spawn one process
per request.

Each frame is:

```text
8 hexadecimal bytes payload length
payload bytes encoded as canonical JSON
```

The length is counted in bytes, not characters. The reader rejects malformed
hex, frames above the negotiated maximum, invalid UTF-8, duplicate critical
keys, trailing data, and unknown required protocol versions. Stderr is bounded
diagnostic output and never part of the protocol.

Raw-byte transport behavior is normatively refined by
`spipe_knowledge_compiler_cooperative_streaming.md`. In particular,
`invalid_utf8` and `frame_too_large` are payload-free local
`TransportDiagnosticV1` classes. Before a complete typed envelope is
host-bound, either class discards decoder state and closes silently; it never
creates a `ProviderResponseV1`, reflects untrusted fields, or enters the bound
provider error vocabulary.

JSON is the interoperability format; equivalent SDN output may be offered for
CLI diagnostics but is not a second wire contract.

Provider discovery is configuration, not `PATH` lookup. SPipe resolves the
configured executable to an absolute canonical path, rejects symlink escape,
and requires the path to match an administrator/user allowlist. Before every
launch it verifies an independently configured artifact digest or trusted
signature whose trust root is not stored beside the executable. File ownership
and permissions must satisfy host policy. A provider-reported build identity is
diagnostic only and cannot establish trust in the provider that reported it.

Launch uses a direct process API, never a shell. The executable path and fixed
argv are separate values; workspace paths, queries, and document content never
enter argv. The child receives a minimal allowlisted environment, a configured
non-writable working directory, explicit stdin/stdout/stderr pipes, and no
inherited credentials, tokens, proxy variables, preload variables, locale
overrides, or unrelated file descriptors. On supported hosts the launcher
closes all non-protocol descriptors and places the provider in its own process
group/job object with CPU time, address-space/RSS, open-file, child-process,
output-byte, and wall-clock limits. Shutdown terminates the whole owned process
group, preventing orphan helpers. Stderr uses a bounded ring buffer with rate
limiting and truncation diagnostics; a provider cannot fill memory or disk by
logging. The provider may not spawn subprocesses or access the network unless a
separately named optional capability and sandbox policy explicitly permits it.

### 4.2 Handshake

Client request:

```json
{"client":"spipe","limits":{"max_frame_bytes":1048576},"operation":"initialize","protocol":{"major":1,"minor":0},"request_id":"1","required":{"analyzer":"spipe-unicode-lex-v1","explanation":"bm25-explain-v1","logical_index":"spipe-lexical-snapshot-v1","provider":"spipe-search-provider/1.0","score":"bm25-fixed-v1"}}
```

The provider response is exactly the full `InitializeResultV1` in Section
14.11 using the closed nested records in Section 14.20. This early overview
does not define a shortened request or response variant.

No request except `initialize` is accepted before a successful handshake.
Capabilities are descriptive and immutable for the process lifetime.

### 4.3 Request envelope

Every request contains:

```text
request_id         opaque client correlation ID
operation          closed operation vocabulary
workspace          stable workspace UID
snapshot           required snapshot or expected parent snapshot
deadline_ms        1..30,000 ms relative to the first accepted header byte
payload            operation-specific object
```

Responses contain the same request ID and operation, `ok`, and exactly one of
`result` or `error`.
Errors have stable code, safe message, retryable flag, and optional details.
Initial operations:

| Operation | Function |
|---|---|
| `index_open` | Load/create a workspace snapshot |
| `index_apply` | Apply bounded add/replace/delete deltas |
| `index_publish` | Atomically publish the next snapshot |
| `search` | Exact/lexical/filter query with cursor |
| `explain` | Explain one result against one snapshot |
| `duplicate_candidates` | Return bounded similarity candidates |
| `symbols_snapshot` | Return compiler-owned symbol snapshot/page |
| `stats` | Return bounded counters and timing summaries |
| `cancel` | Cancel a request ID when supported |
| `shutdown` | Orderly provider shutdown |

Unknown operations fail closed. Mutation requests use a unique operation ID;
replay returns the prior receipt or a conflict if the payload hash differs.

Search responses expose source data for SPipe-owned fusion, not fused results:

```text
source                    lexical or semantic
source_contract           bm25-fixed-v1 or semantic model identity
snapshot and query_receipt
candidate document ID
source_rank               one-based, unique, contiguous
source_score              typed local score; diagnostic to RRF
matched authorized fields and bounded source explanation
next source-local authenticated cursor
```

The provider sorts each source by its local contract and public-ID tie rule.
SPipe validates the page, derives rank from validated order, obtains graph
candidates from its own accepted graph snapshot, removes any pinned identity ID
from all source lists, and executes `rrf-fixed-v1` over the remaining candidates.
A provider cannot receive graph neighborhoods just to fuse them. Lexical and
semantic results are separate typed source pages.

The wrapping `SearchProviderAdapter` treats every provider response as untrusted
input even after binary verification. It requires exactly one outstanding
request with the returned
correlation ID, rejects duplicate/unknown/already-completed IDs, and verifies
the returned workspace, snapshot, score contract, analyzer identity, and query
receipt against the authorized request. Every hit ID must belong to the
request's visible snapshot and pass the caller's visibility policy again before
use. Scores must be finite contract-valid integers within the declared range;
ranks must be unique, contiguous, correctly ordered, and no more numerous than
the requested limit. Cursors, facets, snippets, matched fields, and explanation
terms are accepted only if they refer to authorized records/fields and satisfy
the request hash. Missing or extra critical fields fail the entire response.

Explanations are display data, never trusted markup or instructions. SPipe
validates their typed schema, bounds term/field counts and text bytes, rejects
control characters and embedded resource/command URIs, escapes them for the
target renderer, and reconstructs document title/path/URI from its authorized
artifact graph rather than accepting provider-supplied navigation targets. A
malformed or poisoned explanation discards the full result page and quarantines
the provider snapshot; it is never silently shown with explanation removed,
because that could conceal a compromised response.

### 4.4 Query complexity limits

Protocol v1 has hard maxima, further reducible by configuration or handshake:

| Dimension | Hard maximum |
|---|---:|
| Encoded request or response frame | 1 MiB |
| Normalized query | 4,096 UTF-8 bytes |
| Query tokens | 128 |
| Boolean clauses | 64 |
| Parenthesis/nesting depth | 8 |
| Phrase terms | 32 per phrase, 64 total |
| Prefix/wildcard expansions | 256 total |
| Filters | 32 |
| Values per filter | 64 |
| Requested/returned hits | 1,000 |
| Explanation terms per hit | 128 |
| Explanation fields per hit | 32 |
| Explanation encoded bytes | 64 KiB per hit, 512 KiB per page |
| Index delta documents | 1,000 per frame |
| Document fields | 64 per document |
| Field value | 1 MiB; frame limit still applies |
| Duplicate candidates | 1,000 total, 100 per document |
| Symbol page | 1,000 symbols |
| Client deadline | 1 ms minimum, 30,000 ms maximum |

The parser accounts for expansions before execution and rejects over-budget
queries rather than truncating them into different semantics. Search also has
provider-configured postings visited, candidates scored, CPU, allocation, and
output budgets; exceeding any budget returns `limit_exceeded` or
`deadline_exceeded` with no partial page unless the operation explicitly
negotiated typed partial results. Regex queries and leading unbounded wildcards
are not supported in protocol v1. Duplicate and semantic operations use bounded
candidate buckets and cannot request an all-pairs scan through this hot path.

### 4.5 JavaScript parity

The dependency-free `JsFixedPointSearchProvider` implementation of
`SearchProvider` implements the same logical records, analyzer identity,
`bm25-fixed-v1`, ordering, pagination, error codes, and explanations. It is
in-process and therefore does not implement framing.
`InProcessSearchProviderAdapter` translates its responses into
`LexicalSearchPort`/`SemanticSearchPort` results and runs the shared conformance
vectors. `KnowledgeCompiler` observes only those ports.

Optional capabilities may differ. The selected `SearchProviderAdapter` narrows
features from the provider handshake; `KnowledgeCompiler` never branches on a
provider type and lexical semantics never change with provider availability. A
Simple process-provider crash causes composition to replace
`ProcessSearchProviderAdapter` with `InProcessSearchProviderAdapter` only after
reopening/rebuilding the same logical snapshot and recording a diagnostic.
Results from different score/analyzer contracts never share a cache entry.

## 5. Cache and snapshot identity

### 5.1 Canonical key

Every query cache key hashes:

```text
workspace UID
project UID and revision
worktree UID
published snapshot UID
dirty-overlay generation
analyzer identity
score-contract version
provider implementation/version
normalized query
ordered filters
ordered field names and field weights
fusion contract, k, source_k, ordered participating sources and boost policy
identity-dominance policy and alias-registry generation
limit and cursor
explain flag and explanation version
authorization/visibility scope
semantic model identity when semantic retrieval participates
```

The current PureDatabase key `table|query|limit` is insufficient because it
omits columns, algorithm, and data/index generation. Its replacement includes
database instance, table identity, ordered selected columns, algorithm,
normalized query, limit, MVCC snapshot, and FTS generation.

### 5.2 Storage

Committed content-addressed segments may be shared among worktrees. Dirty
overlays, locks, journals, authorization caches, and cursors are per worktree.
Cache publication uses write-temp, sync according to policy, and atomic rename.
A corrupt or version-mismatched cache is discarded and rebuilt; canonical
project data is never recovered from a derived index.

Cursors are authenticated opaque values containing snapshot UID, query hash,
last score, last document ID, and expiry. A cursor from another snapshot or
authorization scope is rejected.

### 5.3 Invalidation

Parser deltas identify affected document IDs. A content, classification,
visibility, field-weight, analyzer, or alias change creates replace deltas.
Deletion creates tombstones. Changes to analyzer/score/schema identity invalidate
the complete index. Provider restart does not invalidate content-addressed
snapshots when provider and contract identities match.

## 6. Database migrations

### 6.1 DBFS

Current owner: `src/lib/nogc_sync_mut/db/dbfs_engine/fts/`.

Schedule/ownership is fixed: this migration completes in research-plan Wave 4.
Lane C owns `std.common.search` and `bm25-fixed-v1`; lane E owns the DBFS facade,
exact-statistics, and index changes; C+E jointly own golden parity and integration
acceptance. DBFS is not deferred to, repeated in, or re-migrated during Wave 10.
After Wave 4 its common-score facade is a stable dependency for PureDatabase,
textual/server adapters, and provider work.

Migration steps:

1. Add exact `doc_length(doc_id)` and fixed-point corpus-average access.
2. Make `index_document` an idempotent upsert or require explicit replace;
   never append duplicate postings/counts for an existing ID.
3. Replace simplified `fts_bm25_score` internals with common BM25 while keeping
   its signature as a compatibility facade.
4. Make `fts_bm25_search` use exact lengths and public deterministic ID ties.
5. Preserve trigram and Levenshtein modes as distinct operations.
6. Add generation/snapshot identity and bounded top-k; introduce WAND only
   after exhaustive parity passes.

Removal must update exact statistics and not leave logically live tombstones.
Compaction may remove physical tombstones outside the query path.

### 6.2 PureDatabase embedded DB

Current owner:
`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/`.

`PureDatabase` remains transaction owner. Its adapter applies FTS changes only
at the same visibility/commit boundary as rows. Queries bind to one MVCC
snapshot and one matching FTS generation.

Migration steps:

1. Repair search cache identity before changing scoring.
2. Keep `Contains`, `TermFrequency`, and `Bm25` behavior explicitly distinct.
3. Route BM25 through the common scorer/DBFS adapter; remove the duplicate f64
   `_bm25_score` only after direct callers and fallback paths are proven absent.
4. Preserve `bm25_search` and `fts5_search` public facades.
5. Rebuild legacy persisted FTS metadata into the new derived snapshot; do not
   silently interpret an old score/index version as new.
6. Guarantee insert/update/delete/rollback/reopen invalidation and parity.

### 6.3 Textual database

Current owner: `src/lib/nogc_sync_mut/database/fts.spl` plus supported tier
counterparts.

The existing trigram `FtsIndex` remains `contains_fuzzy`. Add a separate BM25
side-index with explicit `search_lexical`; do not change `fts_search` meaning.
Row/WAL mutation and lexical delta form one logical transaction. Recovery
replays the row log, then either validates the side-index generation or rebuilds
it. Derived index persistence never becomes the row source of truth.

Tier variants follow the repository tier-generation/ownership policy. Do not
hand-copy behavior into async/GC tiers without the canonical facade strategy.

### 6.4 Database server

Current owner: `src/lib/nogc_sync_mut/database/server/`.

Add a parent-owned `SearchCapsule` only after extending the closed protocol.
The new operation requires:

- table and explicit permitted fields;
- query, mode, bounded limit, cursor, and deadline;
- session-scoped snapshot identity;
- deny-wins table and field authorization before index/cache access;
- bounded response encoding and cancellation;
- private cache partition keyed by effective capability scope.

Index deltas become visible only after the owning transaction commits. The
chosen durability policy must define whether search-index persistence completes
before acknowledgement or is reconstructable from the durable row/WAL state.
The initial design chooses reconstructable derived segments: durable rows/WAL
are authoritative, publication is ordered after commit, and restart rebuilds or
replays missing segments before serving that snapshot.

Start with exhaustive local top-k. Add immutable segments, WAND, Block-Max
WAND, and shard merge sequentially. Each optimization must match exhaustive
document IDs, ordering, and scores exactly, including ties and deletes.

## 7. Duplicate-analysis extraction

The compiler tool under `src/compiler/90.tools/duplicate_check/` remains CLI
and report owner. Extract only pure reusable facilities:

- normalized content and shingle hashes;
- MinHash and SimHash fingerprints;
- sparse token-frequency vectors and cosine similarity;
- candidate bucketing;
- dense-vector comparison behind internal `SemanticSearchPort`.

Compiler-specific `DuplicationConfig`, `SimpleToken`, filesystem collection,
incremental cache files, Ollama HTTP, formatters, and CLI parsing stay in the
tool and adapt to common records. This avoids making common search depend on
compiler or network/runtime services.

`duplicate_candidates` accepts document IDs, bounded fingerprints/features,
thresholds, maximum candidates per document, and requested methods. It returns
ordered candidate pairs with per-method scores and evidence. Pair ordering is
`score descending, left ID ascending, right ID ascending`. Semantic failure
returns partial lexical results plus a capability diagnostic, never an empty
success that hides the degradation.

The existing duplicate-check corpus, reports, thresholds, and exit codes are
compatibility tests. Extraction is complete only when old CLI results remain
equivalent for pinned fixtures.

## 8. Source-symbol provider

Compiler/HIR data is authoritative for Simple symbols. The provider exports an
immutable, paged snapshot record:

```text
symbol UID
project UID and revision
module and kind
canonical qualified name
display name
normalized signature hash
definition path and byte/line span
reference spans
explicit implements/cover annotations
content hash
visibility/trust metadata
```

Symbol UID derives from compiler-stable identity when available. A rename emits
an alias/supersession relation; it must not rely only on source span. When no
stable compiler identity exists, the export declares the identity provisional
and includes recovery evidence rather than pretending certainty.

`symbols_snapshot` uses compiler data already built for the requested revision
or a cached compiled artifact. It must not compile the entire workspace on each
request. Full compilation/indexing is an explicit maintenance operation;
ordinary reads paginate a published immutable snapshot. Non-Simple languages
use separate analyzers and are never mislabeled compiler-authoritative.

## 9. Failure handling and observability

The single closed wire-error vocabulary and exact operation mapping is Section
14.18. Pre-freeze names are CLI compatibility aliases only and never appear on
the v1 wire: `unsupported_protocol -> protocol_unsupported`,
`analyzer_mismatch -> incompatible_contract`,
`index_corrupt -> snapshot_corrupt`, and `internal -> internal_error`.

Logs never include document bodies, queries from private scopes, credentials,
or raw authorization values. Debug explanations are bounded and redact fields
the caller cannot read.

Counters/timings:

- provider starts, crashes, fallback transitions, and handshake duration;
- snapshot open/build/publish time and bytes;
- delta add/replace/delete count and time;
- query count, P50/P95/P99 latency, candidates scored, postings traversed;
- exact/BM25/graph/semantic contribution counts;
- cache hit/miss/reject-by-identity;
- cancellation/deadline/limit failures;
- exhaustive versus optimized parity probes in verification builds;
- maximum RSS and segment/cache bytes.

Metrics use IDs/scopes safe for the observer and never high-cardinality query
text labels.

## 10. Test design

### 10.1 Golden provider conformance

One checked-in corpus and expected canonical result file drives:

- common Simple exhaustive scorer;
- DBFS facade;
- PureDatabase adapter;
- textual BM25 adapter;
- `JsFixedPointSearchProvider` plus the explicitly limited read-only
  `ReadOnlyJsFallbackSearchProvider`;
- Simple provider wire adapter;
- database server adapter.

Cases cover exact IDs, Unicode, punctuation, stop words, repeated query terms,
multiple fields and weights, zero/one-document corpora, long documents,
deletes/replacements, equal scores, pagination, and explanations. Assertions
compare ordered IDs and integer scores, not approximate floats.

A companion fusion corpus drives SPipe's `rrf-fixed-v1`. Provider adapters are
tested only for source-local ordering and wire conformance. It pins UID/key/
accepted-alias `resolve` short-circuit, general-search rank-1 pinning, removal of
the pinned ID from every RRF source, ambiguity and unauthorized aliases,
one-based fused ranks beginning at final rank 2, `k=60`, source absence, stable ties,
bounded adjustments, semantic degradation, exact fixed-point contributions,
and complete explanations.

### 10.2 Unit and property tests

- Analyzer output and identity are deterministic.
- Clean rebuild equals every valid delta sequence.
- Repeating add/replace/delete is idempotent.
- Deleting or replacing a document updates N, df, lengths, and scores.
- Score accumulation detects overflow.
- `top_k(exhaustive) == WAND == Block-Max WAND` for generated corpora.
- A cursor never crosses snapshot or authorization scope.
- Cache keys differ for columns, algorithm, weights, overlay, provider,
  analyzer, score contract, visibility, and explain mode.
- Duplicate candidate generation is symmetric, bounded, and deterministic.
- Symbol snapshot paging has no duplicate or missing IDs.

### 10.3 Protocol tests

- fragmented and coalesced frames;
- multibyte payload byte lengths;
- malformed hex/JSON/UTF-8 and duplicate critical keys;
- oversize frame/query/result/explanation;
- pre-initialize and repeated initialize;
- unknown operation/capability;
- operation replay with same and conflicting payload hashes;
- deadline, cancellation, provider crash, restart, and fallback;
- stdout contains protocol frames only;
- secret/private content does not appear in errors, stderr, or metrics.
- relative, PATH-resolved, non-allowlisted, symlink-escaped, wrong-digest, and
  invalid-signature provider executables are rejected before execution;
- shell metacharacters in paths/workspaces/queries remain inert, fixed argv is
  unchanged, and hostile environment/preload/proxy/credential variables are not
  inherited;
- unrelated parent file descriptors are closed, child spawning/network are
  denied by baseline policy, and timeout/shutdown kills the complete process
  group or job object;
- CPU, RSS/address-space, file-descriptor, child-count, stdout/frame, and stderr
  ring-buffer limits terminate or reject a malicious provider deterministically;
- unknown, duplicate, replayed, and mismatched response IDs are rejected;
- wrong workspace/snapshot/analyzer/score contract/query receipt is rejected;
- provider-supplied fused ranks, graph/trace boosts, or dominance claims are
  rejected; only typed source-local pages are accepted;
- nonexistent or unauthorized hit IDs/fields/facets/snippets are rejected even
  when the provider assigns them high valid-looking scores;
- negative, overflowing, malformed, out-of-order, duplicate-rank, over-limit,
  and tie-order-violating results are rejected;
- poisoned explanations containing unauthorized fields, oversized arrays/text,
  control characters, markup, instruction text, command/resource URIs, or a
  provider-invented canonical path quarantine the response/snapshot;
- queries at every complexity boundary pass, while one-over-limit query bytes,
  tokens, clauses, nesting, phrases, expansions, filters, values, hits, deltas,
  fields, candidates, symbols, and deadlines fail before expensive execution;
- expansion/postings/candidate/CPU/allocation budget exhaustion returns a
  bounded typed failure and never an uncontrolled partial result.

### 10.4 Database tests

DBFS extends `test/02_integration/storage/dbfs/fts_engine_spec.spl` with exact
length, deterministic tie, upsert, delete, and common-score fixtures.

PureDatabase extends `pure_db_spec.spl`, `pure_db_sql_extended_spec.spl`, and
`db_cache_invalidation_spec.spl` with algorithm/column cache separation,
MVCC rollback, snapshot visibility, checkpoint/reopen, and clean-rebuild parity.

Textual DB tests preserve trigram behavior and separately prove BM25 WAL/update
atomicity. Server unit/system specs prove deny-wins field authorization,
snapshot consistency, durability recovery, bounds, cancellation, private cache
isolation, and optimized/exhaustive parity.

Duplicate-check's current unit, system, and performance suites remain green;
new parity fixtures compare pre-extraction and common-library results. Symbol
tests compare provider exports with compiler definition/reference queries and
exercise rename, overload, deletion, and stale revision behavior.

### 10.5 System scenarios and trace targets

Planned requirements map to these system behaviors:

| Requirement | Scenario evidence |
|---|---|
| Deterministic provider parity | JS and Simple providers return identical golden ordering/scores |
| Safe fallback | Composition swaps process and in-process adapters after a Simple provider crash, with an explicit degradation diagnostic |
| Incremental correctness | mixed deltas equal a clean rebuild at the published snapshot |
| Database isolation | unauthorized fields/documents never influence hits, counts, cache, or explanations |
| Durable server search | restart serves only a reconstructable committed snapshot |
| Reusable duplicate analysis | legacy CLI output parity plus bounded provider candidates |
| Authoritative symbols | exported Simple symbols match compiler-owned definitions/references |

Executable SSpec files and mirrored manuals are created in the implementation
phase after final REQ IDs exist. Tests use built-in matchers and fail-fast
placeholders until their real oracle is implemented.

## 11. Performance and security gates

Wave-0 measurement fixes absolute budgets. Provisional release gates are:

- provider is persistent; zero per-query process spawns;
- no warm-query full-tree scan or repeated source-file read;
- 50,000-document warm lexical query P95 below 100 ms;
- one-document delta publish P95 below 100 ms and at least 20x cheaper than a
  full rebuild on the benchmark repository;
- startup loads a valid snapshot lazily and records time/RSS; it does not
  eagerly compile the workspace;
- WAND/Block-Max WAND return byte-identical ordered IDs and scores to exhaustive;
- duplicate candidate generation is sparse and bounded, never global all-pairs;
- provider request/response, index, cache, and RSS limits are enforced under
  adversarial input;
- authorization occurs before postings, corpus statistics, caches, snippets,
  or explanations can reveal protected material;
- remote semantic calls are disabled by default and require explicit policy;
- private content never uses public MCP/provider cache scope.

A change that improves latency but changes result parity, visibility, snapshot
semantics, or deterministic ordering fails verification.

## 12. Implementation sequence and gates

1. **Contract freeze:** logical records, analyzer/score identities, golden corpus,
   exhaustive oracle, identity dominance, and SPipe-owned `rrf-fixed-v1` with
   lexical/graph sources. Gate: Simple/JS BM25 source ranking agrees and
   provider-independent SPipe fusion/dominance fixtures pass.
2. **Common index:** document/stats/query/explain/snapshot ports and idempotent
   deltas. Gate: clean/incremental property parity.
3. **DBFS adapter:** exact lengths, common scorer, stable ties, compatibility
   facades. Gate: existing plus golden DBFS tests.
4. **PureDatabase adapter:** cache repair, MVCC generation, facade migration.
   Gate: insert/update/delete/rollback/reopen parity.
5. **Textual adapter:** retain trigram API, add transactional BM25 side-index.
   Gate: WAL/recovery and semantic separation.
6. **Duplicate extraction:** pure common primitives with compiler orchestration
   unchanged. Gate: pinned CLI/report parity and performance non-regression.
7. **Provider executable:** bounded protocol, persistent lifecycle, search,
   duplicate, and symbol handlers. Gate: protocol/security/native entry-closure
   smoke and `JsFixedPointSearchProvider` parity.
8. **Database server:** capability/snapshot/durability contract, exhaustive
   implementation. Gate: leakage, recovery, bounds, and concurrency tests.
9. **Optimizations:** segments, WAND, Block-Max WAND, optional ANN/semantic and
   sharding, one at a time. Gate: exact exhaustive parity plus measured benefit.

These numbered items are dependency stages inside this design, not replacements
for the research plan's waves. Stages 1-3, including the complete DBFS migration,
belong to Wave 4 under lane C, lane E, and the C+E integration gate described in
Section 6.1. Research-plan Wave 10 may add database-server execution strategies
and optional semantic sources against the frozen `LexicalSearchPort` and DBFS
facade. It must not reopen DBFS scoring/storage migration. Any later incompatible
change requires a new score-contract version and an explicit migration plan,
not an implicit Wave-10 rewrite.

No later wave repairs an earlier contract silently. A required contract change
increments its version, regenerates the golden corpus explicitly, documents the
migration, and prevents mixed-version cache reuse.

## 13. Completion checklist

- One documented `bm25-fixed-v1` implementation contract governs all adapters.
- Exact lengths and deterministic public-ID tie-breaking are used everywhere.
- The JavaScript fallback executes only its admitted read-only conformance
  cells (01, 02, 03, 04, 11, 15, 16, and 22); its fixed
  `(scope_digest,logical_root)` binding is checked before every read and it
  has no open/apply/publish/lifecycle/authority mutation surface. The Simple
  provider remains responsible for the full process/lifecycle matrix.
- Provider startup, hot request, cache, invalidation, bounds, and fallback paths
  have executable evidence.
- PureDatabase cache identity includes columns, algorithm, and generation.
- DB server search is field-authorized and snapshot-consistent before release.
- Duplicate primitives no longer require compiler ownership, while the legacy
  CLI remains compatible.
- Simple symbol export is compiler-authoritative and revisioned.
- Every optimized path matches the exhaustive oracle.
- Performance and security gates pass without embeddings or a remote service.

## 13.1 W4A provider-conformance closure plan

This is the implementation plan that closes the gap between the frozen Wave 4
contract and an admitted provider.  **W4A is not a second score contract and
does not reopen `bm25-fixed-v1`.**  It is a staged adapter-conformance program.
No target is called conformant merely because it can compile a probe or returns
the golden three-document result.  A target is admitted only after the
conformance record in Section 13.1.5 has all required cells and its exact
logical-root/scope bindings verify.

### 13.1.1 Starting evidence and ownership

The current source supplies useful but deliberately narrow starting points:

| Existing path | What it proves | What it does not prove |
|---|---|---|
| `src/lib/common/search/{analyzer,document,corpus_stats,ranking,query,snapshot,top_k,provider,explain}.spl` | common records, checked fixed-point scoring, immutable snapshot records and port vocabulary | a process transport or a database transaction boundary |
| `src/lib/nogc_sync_mut/db/dbfs_engine/fts/wave4_compatibility.spl` | an exhaustive, public-single-scope five-field DBFS compatibility projection | arbitrary visibility scopes, cursors, provider framing, or DBFS as a `SearchProvider` |
| `src/app/spipe_knowledge_provider/{lexical,service,protocol,wire_*,byte_stream,frame_*,request_control,work_control}.spl` | the intended native executable and framed-service ownership split | native provider admission, successful Stage 4 executable provenance, or qualified performance |
| `examples/05_stdlib/spipe/src/provider/{protocol,adapter,js_fixed_point}.js` | normative dependency-free provider/adapter validation shape | a process adapter, native binary authenticity, or fallback evidence |
| `examples/05_stdlib/spipe/test/support/{simple_provider_wave4_parity_probe,dbfs_wave4_parity_probe}.spl` | locked micro-corpus oracle observations | all W4 cells, hostile-wire behavior, multi-scope isolation, or a functional receipt |

Lane C owns only `src/lib/common/search/**`; lane D owns the SPipe JavaScript
adapter/process boundary and fixture checker; lane E owns DBFS compatibility;
each database owner owns its own transactional adapter.  `src/app/
spipe_knowledge_provider/**` is a Simple-provider lane with a published wire
contract, not a substitute for either DBFS or database-server ownership.  A
single merge owner updates the corpus digest, contract manifest, and evidence
checker only after independent review.

### 13.1.2 Required conformance record and common fixture

Track one immutable fixture directory:

```text
examples/05_stdlib/spipe/test/fixture/wave4_search/
  fixture_manifest.json
  golden_corpus.json
  bm25_intermediates.json
  golden_results.json
  provider_protocol_vectors.json
  conformance_applicability.json
  conformance_evidence_schema.json
```

`fixture_manifest.json` must hash every listed file, name the five contract
identities, and record the exact public document-ID byte ordering.  A target
first transforms its native rows/documents into canonical `SearchDocumentV1`
bytes and proves the resulting `spipe-lexical-snapshot-v1` root; it then runs
the same query/delta vectors.  The checker recomputes roots, statistics,
scores, explanation digests, rank/tie ordering, and page hashes from the
checked-in oracle rather than accepting target-reported `pass` booleans.

Every emitted `ProviderConformanceRecordV1` is closed canonical JSON:

```text
{schema, fixture_manifest_sha256, target_id, target_build_identity,
 provider_contract, analyzer_contract, score_contract, explanation_contract,
 logical_index_contract, capability_set, scope_digest, logical_root,
 query_result_digests, delta_result_digests, explanation_digests,
 executed_cells, unsupported_cells, process_evidence, security_evidence,
 generated_at_utc, checker_version, record_sha256}
```

`target_build_identity` is an executable digest plus Stage 4 provenance for
the native process target, and a canonical source/module digest for in-process
targets. `unsupported_cells` is allowed only when the applicability manifest
marks the exact target/capability combination as out of scope; it never turns a
required lexical, scope, delta, or explanation cell into a pass.  `record_sha256`
hashes the same closed object with that field zeroed.  Receipt storage is
derived evidence under `build/test-artifacts/spipe-wave4/`; checked-in fixtures
contain only reproducible inputs and expected oracle values.

### 13.1.3 W4A sequence: JS, Simple native, and process adapter

| W4A stage | Exact implementation scope | Required proof before the next stage |
|---|---|---|
| W4A-1 contract oracle | C: `src/lib/common/search/**`; D: golden fixture/checker only | checked arithmetic/intermediate vectors, Unicode analyzer parity, add/replace/delete clean-rebuild equality, explanation recomputation |
| W4A-2 JS baseline | D: `examples/05_stdlib/spipe/src/provider/{protocol,adapter,js_fixed_point}.js` and `src/index/**` only | initialized `InProcessSearchProviderAdapter` passes every applicable lexical/source-page vector and rejects bad bindings without cache publication |
| W4A-3 native lexical core | Simple provider lane: `src/app/spipe_knowledge_provider/{lexical,service,protocol,wire_query,wire_dispatch,wire_core}.spl` | the native core consumes the canonical logical snapshot and returns byte-equivalent source-local pages/explanations; no adapter/RRF code is copied into Simple |
| W4A-4 framed process adapter | D: new `examples/05_stdlib/spipe/src/provider/process_adapter.js` plus private launch helper; Simple: only `main.spl`/byte-stream framing hooks | one long-lived, shell-free child generation initializes once, carries one request/snapshot/scope binding per frame, and has no per-query spawn or cursor cross-generation reuse |
| W4A-5 degradation | D composition only | crash/timeout/malformed native reply quarantines that generation, opens or rebuilds the same logical root in JS, retries once, and emits a bounded diagnostic; root mismatch returns no result and does not fall back |
| W4A-6 admission | integration/checker/guide only | exact record plus independent review; no performance or production-readiness claim without the qualified receipt |

The process adapter receives the *already authorization-filtered* logical
snapshot and an opaque request binding, never raw workspace paths, filesystem
handles, registry credentials, or graph/trace material.  It launches a
configured canonical executable with fixed `argv`, fixed nonsymlink working
directory, explicit minimal environment allowlist, closed inherited file
descriptors, resource/deadline/output limits, and process-group cleanup.  It
checks executable ownership/mode and an approved binary/provenance digest
before launch.  It sends only canonical framed bytes; it validates native
responses before cache insertion against the request ID, operation, provider
generation, implementation digest, logical root, scope digest, query digest,
cursor digest, visible document membership, score/order/explanation rules, and
page limits.  An invalid frame/response is a generation quarantine, not a
candidate-level warning.

The adapter may invoke exactly one JS retry only for a transport crash,
deadline, or quarantine *after* proving the JS snapshot root and all five
lexical identities equal the request binding.  It must not retry semantic
`ProviderErrorV1`, switch providers within a paged collection, merge native and
JS hits, re-use a native cursor, or turn a failed native request into a cache
hit.  `phrase`, `regex`, `wildcard`, semantic, duplicate, and symbols remain
separately negotiated capabilities; no unavailable capability is emulated as a
lexical success.

### 13.1.4 Database adaptation order

Database implementations consume the same fixture but do **not** become
SPipe's process provider merely by adopting the scorer.

| Target | Owner and changes | Snapshot/scope rule | Required compatibility and recovery proof |
|---|---|---|---|
| DBFS (Wave 4) | E changes `src/lib/nogc_sync_mut/db/dbfs_engine/fts/{bm25,inverted_index,search,wave4_compatibility}.spl`; C changes common scorer only | `DbfsWave4Index` must bind exactly one scope and root; production DBFS must reject a foreign scope before postings/statistics | public `FtsEngine`/`fts_bm25_*` behaviors stay distinct from trigram/fuzzy modes; upsert/delete update exact N/df/length; facade and common oracle match; compaction preserves live root |
| PureDatabase (Wave 10) | pure-SQL owner changes `src/lib/nogc_sync_mut/database/pure_sql/{database,__init__}.spl` and its `_PureDatabase/**` internals only | row transaction commits an FTS generation atomically with the visible MVCC version; query cursor contains DB instance/table/columns/algorithm/MVCC/FTS generation/scope | insert/update/delete/rollback/checkpoint/reopen clean-rebuild parity; `Contains`, term-frequency, BM25, and `fts5_search` retain separately tested behavior; old metadata rebuilds instead of being reinterpreted |
| Textual DB (Wave 10) | textual owner changes `src/lib/nogc_sync_mut/database/{fts,wal,core}.spl` plus tier-approved counterparts | rows/WAL are authority; BM25 side-index is derived and cannot become visible before its committed row generation | retain trigram `fts_search` as `contains_fuzzy`; add explicit `search_lexical`; fault/restart replay validates or rebuilds side index; no unlogged row/index split |
| Database server (Wave 10) | server owner changes `src/lib/nogc_sync_mut/database/server/{capability,session,txn,durability,protocol,transport,server}.spl`, adding a private SearchCapsule | authorize table/fields before postings/stats/cache, bind every request/cursor to session MVCC snapshot and effective-capability digest | deny-wins leakage tests for hit/count/facet/explanation/cache; commit/restart reconstruction; cancellation, bounded pages, private cache partitions; exhaustive parity before WAND/Block-Max WAND/shard merge |

The DBFS compatibility probe is a valuable W4A input but not evidence that its
single-public scope is sufficient for PureDatabase, textual, or server search.
No database implementation may expose a `SearchProvider` wire capability until
it independently meets the process-provider scope/binding and transport gates.
WAND, Block-Max WAND, ANN, or shard merging are separate opt-in implementations:
each has generated-corpus exhaustive equivalence, delete/tie/cursor parity,
and a measured benefit before selection.

### 13.1.5 Mandatory gate matrix

| Gate | JS | Simple native/process | DBFS | PureDB/textual/server |
|---|---:|---:|---:|---:|
| canonical document/root/statistics and BM25 intermediate parity | required | required | required | required before adapter admission |
| Unicode 17 analyzer and five-field ordering | required | required | required | required |
| add/replace/delete/no-op/replay clean-root parity | required | required | required | required with native transaction/recovery cases |
| exact source-local ranks, scores, ties, explanations and cursors | required | required | required where cursor supported | required |
| foreign scope/snapshot/query/cursor/document rejection | required | required | scope-only W4 facade; full native scope before exposure | required |
| hostile framed wire, launch, child-limit and timeout controls | N/A in-process | required | N/A facade | required only if remotely/process exposed |
| no per-query spawn/full-tree scan/repeated unchanged source read | required by qualified collector | required by qualified collector | measured if selected for SPipe | measured per exposed service |
| transaction/MVCC/WAL/restart/durability proof | N/A derived in-process | provider lifecycle only | DBFS supported persistence boundary | required |
| exact exhaustive versus optimization parity | oracle | oracle | before WAND | before each optimization |

For the Simple process target, `executed_cells` is exactly W4-SRCH-01 through
W4-SRCH-08 and W4-SRCH-10 through W4-SRCH-39, once each in numeric order;
W4-SRCH-27 is mandatory and must not be omitted. Streaming/control cells 28
through 39 include the Stage-4/import/production-controlled closures 38 and
39 and are functional prerequisites, not optional performance observations.
JS and DBFS records may use the frozen applicability manifest only for genuinely
nonapplicable process cells; `unsupported_cells` cannot omit a required target
cell or silently downgrade it. W4-SRCH-09 is qualified-performance evidence
and cannot be self-certified by the provider. A build that cannot execute an
applicable cell records `NOT EVIDENCE`, not a partial PASS.

### 13.1.6 Security, performance, and closure conditions

Before W4A-6, run one process-adapter adversarial suite covering path and
symlink substitution, digest/provenance mismatch, hostile environment and
preload variables, shell metacharacters, inherited descriptors, oversize and
fragmented frames, invalid UTF-8/JSON, duplicate keys, replayed/mismatched
request IDs, cross-scope/snapshot cursors, extra or unauthorized document IDs,
score/tie/explanation forgery, provider hang/crash, process-tree escape, and
output/RSS/CPU/FD limits.  Every failure must produce either a payload-free
transport diagnostic before envelope binding or the closed operation error
after binding; neither may disclose private query/content values.

Qualified performance follows Section 14.6 exactly: a Stage 4 admitted native
binary, one persistent provider, approved containment counter journal, one
warmup plus at least 20 alternating samples, and the functional receipt as a
verified prerequisite.  The W4A closure packet contains the conformance record,
qualified receipt (or explicit `NOT EVIDENCE`), raw counter journal digest,
native binary/provenance digest, fixture manifest digest, commands/exit codes,
applicability matrix, and independent-review verdict.  Until all required
functional cells pass, W4 remains open.  Until the qualified receipt passes,
the implementation may be functionally admitted but must not claim NFR
performance completion or production availability.

## 14. Wave 4 normative contract freeze

<!-- codex-design -->

This section incorporates the completed Wave 4 provider, Simple-search, and
acceptance-evidence audits. It is normative for Wave 4. Where earlier
descriptive text leaves a choice open, the closed values below control. An
incompatible change requires a new contract identifier, migration, fixtures,
and explicit cache/index invalidation; it must not silently reinterpret a v1
snapshot.

### 14.1 Frozen identities and fields

| Contract | Exact identity |
|---|---|
| Provider | `spipe-search-provider/1.0` |
| Analyzer | `spipe-unicode-lex-v1` |
| Score | `bm25-fixed-v1` |
| Explanation | `bm25-explain-v1` |
| Logical index | `spipe-lexical-snapshot-v1` |
| Fusion | `rrf-fixed-v1` |

`SearchDocumentV1` has the closed, ordered fields below. Each field occurs
exactly once; unknown, duplicate, or reordered fields are rejected at a trust
boundary. The weights are contract data, not provider configuration:

| Ordinal | Field | Weight milli |
|---:|---|---:|
| 0 | `identifier` | 4000 |
| 1 | `title` | 4000 |
| 2 | `heading` | 2500 |
| 3 | `classification` | 2000 |
| 4 | `body` | 1000 |

Canonical `SearchDocumentV1` is exactly
`{document_id, revision, fields, facets, visibility_digest, content_hash}`.
`fields` contains the five closed entries in the table order; `facets` sorts by
unsigned UTF-8 `(name,value)`. Logical identity and hashing use canonical UTF-8
JSON; storage ordinals, postings, segment boundaries, tombstone layout,
provider implementation/version, and physical file paths are excluded. The
external acceleration interface remains only `SearchProvider`; internal
consumers see `LexicalSearchPort` and optional `SemanticSearchPort`. The
dependency-free implementation identifies as `spipe_js` behind
`InProcessSearchProviderAdapter` rather than creating another interface.

### 14.2 `spipe-unicode-lex-v1`

Input must be valid UTF-8. Analysis applies NFC, then Unicode default lowercase
using the exact Unicode data-table revision shipped and named by the analyzer
implementation. A release cannot claim `spipe-unicode-lex-v1` parity until the
dependency-free JavaScript and Simple implementations use the same pinned table
and pass every scalar-value fixture; ASCII-only approximation is a failed
implementation gate.

A token is a maximal sequence of Unicode `Alphabetic`, `Decimal_Number`, or
`Mark` code points, plus `_`. Identifier fields additionally retain the full
normalized field value as one exact token. Token positions advance before
stop-word removal, so removing a stop word cannot collapse positional gaps.
There is no stemming. The existing English stop-word set is frozen and
hash-locked as `en-basic-v1`; analyzer identity includes its hash and the pinned
Unicode table.

Wave 4 query v1 is a bag of distinct analyzed terms plus equality facets.
Phrase evaluation is not implemented or advertised: handshake capability is
`phrase=false`, and phrase syntax returns `unsupported_capability`. Later
phrase support requires a new query/analyzer contract and position-parity
fixtures rather than opportunistic behavior under v1. Regex and wildcard
capabilities are likewise `false`. Accepted hard bounds are 4,096 UTF-8 query
bytes, 128 analyzed tokens, 32 filters, 64 values per filter, and 1,000 hits.

### 14.3 Checked `bm25-fixed-v1`

Statistics are per field: `N`, `df`, document length, and average length.
`N` counts all live documents in the field corpus; a live document missing a
field contributes length zero. Deleted documents contribute nothing. The
scorer uses `SCALE=1_000_000`, `k1=1_200_000`, and `b=750_000`, with the
non-negative IDF already specified in Section 3.4. Natural logarithm uses the
existing seven-term atanh series extended through the `p13` term and
`LN2=693147`.

Every add, multiply, shift, division precondition, narrowing conversion, corpus
statistic, and accumulator is checked. Overflow, zero/negative denominators,
invalid `df/N`, or noncanonical arrays return a typed error and publish no
result (`score_overflow` for arithmetic overflow). Division truncates toward
zero. Internal score arithmetic remains at contract scale; conversion to the
public `Score` milli representation happens exactly once after all weighted
field contributions are accumulated. Results sort by score descending, then
by ascending unsigned UTF-8 bytes of public document ID. `bm25-explain-v1`
records canonical per-field/per-term inputs, intermediate checked values,
weighted contribution, final conversion, and the applied tie rule; bounded
explanations must recompute to the returned score exactly.

### 14.4 Logical snapshots and deltas

The graph-independent logical root is:

```text
sha256(canonicalJson({
  contract: "spipe-lexical-snapshot-v1",
  analyzer: "spipe-unicode-lex-v1",
  score: "bm25-fixed-v1",
  scope_digest,
  documents: ScopedSearchDocumentV1 sorted by unsigned UTF-8 document ID bytes
}))
```

Clean builds and all equivalent incremental histories must produce that same
root regardless of provider or physical index layout. An `IndexDeltaV1` binds
base logical root, result logical root, and three UID-disjoint, canonically
sorted sets: `add` carries the complete new document; `replace` carries the
complete new document plus expected prior revision and document hash; `delete`
carries a document ID plus either an exact expected prior revision/hash pair or
the paired null absence assertion defined in Section 14.12. The delta has a
canonical operation ID and payload hash. Byte-identical replay returns the
original byte-identical result envelope and receipt: replay is not a distinct
result status or receipt outcome. A reused operation ID with different bytes
is conflict.
Publication linearizes through the one combined parent transaction defined in
Section 14.17. For `published`, its compare-and-swap atomically commits the
current-root pointer, terminal candidate record, signed operation receipt, and
publication metadata after candidate documents/statistics are durable. None of
those four records is separately visible. `stale_base` and `aborted` atomically
commit candidate plus receipt without changing the root pointer.

### 14.5 Provider framing, health, and fallback

Wire frames are exactly eight **lowercase** hexadecimal ASCII length bytes
followed immediately by canonical UTF-8 JSON. Maximum payload is 1 MiB before
allocation or decoding; uppercase hex, malformed length, invalid UTF-8,
noncanonical JSON, trailing bytes, and oversize frames fail closed.

The adapter state machine is closed:

```text
new -> initializing -> healthy -> quarantined | unavailable -> closed
```

`quarantined` and `unavailable` may transition to `closed`; recovery creates a
new provider generation and repeats initialization. A malformed, mismatched,
poisoned, or unauthorized response quarantines the whole generation and
invalidates all of its pending results and cursors. A crash or failed health
check may fall back once to `JsFixedPointSearchProvider`: SPipe rebuilds or
opens the same logical snapshot, proves the same logical root, records the
degradation, and retries the logical request at most once. It never merges
provider generations, resumes half a page, reuses a process-provider cursor,
or returns a mixed page. If root parity cannot be proved, the operation returns
`provider_unavailable` without results.

Health is proven by successful initialization plus a bounded contract/root
probe, not merely by process liveness. Provider identity, the five provider-side
contract IDs, capabilities (including `phrase=false`), limits, generation, and
logical root bind every request, response, cursor, cache entry, and receipt.
SPipe binds adapter-local `rrf-fixed-v1` separately after provider validation.
The canonical initialization result is exactly `InitializeResultV1` from
Section 14.11, with the closed nested records and identical field set specified
once in Section 14.20; this section defines no second or shortened schema. A
major or semantic contract mismatch fails initialization. Unknown minor-version
fields are accepted only when the response declares them optional. The adapter validates
workspace, snapshot, query receipt, visible membership, authorization,
score/order/ties, explanations, and limits on every response.

Timeout/crash fallback emits a stable `SPK4xx` degradation diagnostic. Semantic
failure removes only the semantic candidate source and remains explicit in the
diagnostic and fusion explanation; it does not quarantine an otherwise valid
lexical provider generation.

### 14.6 Qualified performance evidence

Performance is evidence only when its receipt records machine/CPU and memory,
OS, toolchain, build identity/mode, provider identity, all contract versions,
fixture hash and sizes, warm-up count, measured sample count, percentile method,
raw samples, P95, maximum RSS, command, exit status, and timestamp. Functional
parity, bounds, and absence of per-query spawning/full-tree scans are hard
gates independent of timing. No provisional absolute latency or capacity value
in this document may be reported as PASS until a checked-in benchmark profile
qualifies the hardware, dataset, warmups, samples, variance rule, and budget.
`measureQualifiedSearch` is the sole system-test helper allowed to issue a
qualified performance receipt. Its one frozen signature is
`measureQualifiedSearch(profile_path, fixture_path, operation_plan_path,
functional_receipt_uri, output_path)`. Each path is absolute, canonical, and
nonsymlink; `functional_receipt_uri` is a canonical `file://` URI resolving to
such a path. There is no overload, implicit provider/repetition argument, or
environment-derived fallback: provider identity and counts come from the
hashed profile and operation plan.

The initial qualification fixture is 50,000 artifacts, 1,000,000 graph nodes,
10 linked projects, and 5 worktrees. It uses one warm-up followed by at least
20 alternating full-rebuild and one-document-update samples. Once its profile
is checked in, the conditional gates are warm query P95 below 100 ms,
one-document update P95 below 100 ms, and median full rebuild divided by median
one-document update at least `20.0`. Peak RSS/index/cache budgets come from that
profile. Degradation measurements are separate from steady-state samples.

#### 14.6.1 Minimal qualified receipt contract

The checked-in profile is one closed canonical-JSON
`QualifiedSearchProfileV1` object. Unknown, missing, duplicate-normalized, or
wrong-typed fields make the host unqualified:

```text
schema = "spipe-qualified-search-profile-v1"
id = nonempty ASCII identifier
budget_version = nonempty ASCII identifier
subject = {implementation, provider_id, provider_version,
           protocol_version, analyzer_id, score_id}
host = {os, kernel, architecture, cpu_model,
        logical_cpu_count_min, logical_cpu_count_max,
        memory_bytes_min, core_policy}
core_policy = {mode = "exclusive-cpuset" | "scheduler-default",
               logical_cpu_ids, simultaneous_multithreading,
               frequency_governor}
adapter = {counter_adapter_id, counter_adapter_version,
           os, architecture, containment_kind, peak_rss_counter,
           syscall_observer, journal_schema = "spipe-counter-journal-v1"}
fixture = {id, sha256, artifact_count, graph_node_count, token_count,
           content_bytes, linked_project_count, worktree_count,
           snapshot_sha256, query_plan_sha256, query_count_per_sample}
method = {warmup_count, sample_count,
          percentile = "nearest-rank-ceil-v1",
          median = "lower-middle-v1", variance_rule}
variance_rule = {metric = "warm-query-p95-ns",
                 max_median_absolute_deviation_milli,
                 maximum_discarded_samples = 0}
budgets = {warm_query_p95_ns_max,
           one_document_publish_p95_ns_max,
           rebuild_to_publish_ratio_milli_min,
           max_rss_bytes_max, index_bytes_max, cache_bytes_max}
```

Every count, byte value, duration, logical CPU ID, and fixed-point milli value
is a non-negative JSON safe integer. Counts and budget maxima are positive;
`warmup_count >= 1`, `sample_count >= 20`, and the logical CPU list is sorted,
unique, and within the declared inclusive CPU-count range. Host strings compare
byte-for-byte; no regex, prefix, family, or “equivalent machine” matching is
permitted. The observed host must match OS, kernel, architecture, CPU model,
core policy, and adapter identity exactly, its CPU count inclusively, and its
memory at or above `memory_bytes_min`. The collector observes these values; it
does not copy them from the profile. `scheduler-default` requires an empty CPU
list; `exclusive-cpuset` requires proof of exclusive affinity to exactly the
listed IDs. The variance rule uses the unmodified warm-query samples and
integer lower-middle medians: `floor(1000 * MAD / median)`. A zero median or a
value above the limit is `not_evidence`. Samples are never discarded,
winsorized, retried, or substituted.

`measureQualifiedSearch(profile_path, fixture_path, operation_plan_path,
functional_receipt_uri, output_path)` returns exactly one
`QualifiedSearchReceiptV1` only after Stage 4 admission and every functional
prerequisite succeeds. It returns a typed `not_evidence` diagnostic and writes
no receipt when the binary/provenance pair is absent, fails admission, the
fixture or query-plan hash differs, the provider exits nonzero, a sample is
missing, an activity guard is nonzero, or any bound is exceeded. An observation
file must never be relabeled as this receipt.

The canonical JSON object is closed and contains these fields:

```text
schema = "spipe-qualified-search-receipt-v1"
profile = {id, sha256, budget_version}
subject = {implementation, provider_id, provider_version,
           protocol_version, analyzer_id, score_id}
executable = {canonical_path, sha256, build_mode,
              stage4_provenance_path, stage4_provenance_sha256,
              toolchain_id, toolchain_version, toolchain_sha256,
              collector_runtime_id, collector_runtime_version,
              collector_runtime_sha256}
host = {os, kernel, architecture, cpu_model, logical_cpu_count,
        core_policy, memory_bytes, clock_source, rss_counter_source}
fixture = {id, sha256, artifact_count, graph_node_count, token_count,
           content_bytes, linked_project_count, worktree_count,
           snapshot_sha256, query_plan_sha256, query_count_per_sample}
method = {collector_version, command_argv, environment_allowlist,
          warmup_count, sample_count, percentile = "nearest-rank-ceil-v1",
          rss_scope = "qualified-containment-tree-peak-bytes",
          operation_plan_path, operation_plan_sha256,
          counter_adapter_id, counter_adapter_version}
samples = {warm_startup_ns, warm_query_ns,
           one_document_publish_ns, full_rebuild_ns, timed_queries}
summary = {warm_query_p95_ns, one_document_publish_p95_ns,
           full_rebuild_median_ns, one_document_publish_median_ns,
           rebuild_to_publish_ratio_milli, max_rss_bytes,
           index_bytes, cache_bytes}
guards = {provider_start_count, per_query_spawn_count,
          warm_full_tree_scan_count, warm_repeated_source_read_count,
          counter_evidence_uri, counter_evidence_sha256,
          functional_conformance_receipt_uri,
          functional_conformance_receipt_sha256}
result = {exit_status, started_at_utc, completed_at_utc}
```

All durations and byte counts are non-negative JSON safe integers; ratios are
fixed-point integers. `warm_startup_ns` is one scalar for opening the admitted
warm snapshot. Update and rebuild arrays contain exactly `sample_count`
entries. `warm_query_ns` contains exactly
`sample_count * query_count_per_sample` entries in hashed-plan order: every
repetition executes the full query plan against one persistent provider, but
each request is timed separately. P95 is the sorted per-request sample at
one-based rank `ceil(0.95 * n)` and median uses the lower middle sample for even
`n`. `max_rss_bytes` is the maximum resident set of the qualified containment
tree from provider launch through clean shutdown, obtained from the
profile-approved OS peak counter named by `rss_counter_source`; heap size or
periodic best-effort sampling is not a substitute. Before provider launch, the
collector creates and seals a dedicated platform containment object and starts
the independent counter adapter. Every provider child and descendant is
enrolled at creation. Membership survives ordinary reparenting and is retained
until every enrolled process exits; launch, exec, fork/spawn, reparent, exit,
and peak-RSS events remain attributable even when a descendant outlives its
parent. An adapter unable to prove pre-launch enrollment, descendant coverage,
reparent retention, event-loss detection, and terminal enumeration fails
closed as `not_evidence`.

`timed_queries` has the same cardinality and order as `warm_query_ns`. Each
closed record is `{round_index, query_index, query_id,
expected_result_sha256, observed_result_sha256, status, duration_ns}`. Indices
are zero-based safe integers; the query ID and expected digest come from the
hashed operation plan; the observed digest is SHA-256 of the exact canonical
response bytes after normal conformance validation. `status` has the sole
qualified value `matched`, both digests are 64 lowercase hexadecimal bytes and
equal, and `duration_ns` equals the corresponding raw duration. Timeout, error,
rejection, mismatch, omission, or reordering invalidates the whole receipt.

`rebuild_to_publish_ratio_milli` uses checked widened integer arithmetic:
`floor((full_rebuild_median_ns * 1000) /
one_document_publish_median_ns)`. Overflow or a zero denominator is
`not_evidence`; floating point and nearest rounding are forbidden. The initial
`20.0` gate is the integer comparison `>= 20000`.

The guard counters are computed by that independent adapter, never provider
self-report. `provider_start_count` counts admitted provider launches;
`per_query_spawn_count` counts process creations within a query interval;
`warm_full_tree_scan_count` counts fixture-workspace root enumerations during
warm query intervals; and `warm_repeated_source_read_count` counts second or
later content reads of an unchanged source path in those intervals. The
adapter emits a canonical append-only journal with sequence numbers, monotonic
timestamps, request/operation attribution, and a SHA-256 predecessor chain.
The checker resolves its canonical `file://` URI, verifies its terminal hash,
replays membership and intervals, recomputes all guards and peak RSS, and
rejects chain failure, event loss/overflow, unsupported adapters, or any
provider-authored counter.

The journal is canonical UTF-8 JSON Lines: exactly one canonical JSON object
plus one LF per line, with no BOM or CR. It begins with the closed header
`{schema = "spipe-counter-journal-v1", journal_id, adapter_id,
adapter_version, host_boot_id, monotonic_clock_id, workspace,
containment_identity, first_sequence = 0, lost_event_count = 0}`. `workspace`
is `{canonical_path, path_identity_kind, volume_or_device_id,
file_id_or_inode}`. Its identity is captured from an opened nonsymlink root
handle before launch; path events are classified by handle-relative identity,
never textual prefix.

Each closed event is `{sequence, monotonic_ns, event, process_id,
process_start_identity, parent_process_id, request_id, operation_id,
path_identity, bytes, source_version, source_content_sha256,
source_change_witness, predecessor_sha256}`, where the closed witness is
`{kind, identity_generation, size_bytes, modified_time_ns, witness_sha256}`.
Nonapplicable fields use their typed zero or empty-string sentinel and are never
omitted or null. Sequence numbers are contiguous from zero. The first
predecessor is 64 zeroes; each later value is SHA-256 of the preceding line
bytes including LF. The event enum is `containment_create`, `process_launch`,
`process_exec`, `process_spawn`, `process_reparent`, `process_exit`,
`query_begin`, `query_end`, `workspace_enumerate`, `source_open`,
`source_change`, `rss_peak`, `adapter_overflow`, and
`containment_enumerate`.

`workspace_enumerate` means an OS enumeration whose opened directory handle is
the workspace-root identity. `source_open` means a successful read-capable open
of a fixture-source identity.

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

Process creation follows successful kernel create/spawn/fork/clone semantics;
exec does not add a process and failed syscalls do not increment a counter. The
approved adapter observes these OS semantics rather than inferring them from
provider logs.

The final closed trailer is `{schema =
"spipe-counter-journal-terminal-v1", journal_id, event_count, last_sequence,
lost_event_count, live_process_count, terminal_membership_sha256,
predecessor_sha256, terminal_sha256}`. Its predecessor hashes the last event
line. `terminal_sha256` hashes the trailer's canonical bytes with that field
temporarily set to 64 zeroes, excluding its final LF. The receipt's journal
hash covers the complete stored bytes including every LF. Overflow, nonzero
loss/live count, gaps, unknown events, path-identity ambiguity, incomplete
terminal enumeration, or predecessor/terminal mismatch is `not_evidence`.

`provider_start_count` must equal `1`; the other three activity counters must
equal `0`. The functional-conformance receipt URI names the exact successful
Wave 4 receipt produced before timing, and its bytes must match
`functional_conformance_receipt_sha256`. The checker revalidates its subject,
executable, fixture, scope, completed matrix, and success status. That matrix
contains each required `W4-SRCH-01` through `W4-SRCH-08` and `W4-SRCH-10`
through `W4-SRCH-14` ID exactly once in ascending numeric order, with no other
ID; it explicitly excludes performance cell `W4-SRCH-09`. Ordering is acyclic:
functional conformance produces this receipt first, then qualified performance
consumes it and alone evaluates `W4-SRCH-09`; cell 09 is never a prerequisite
of the receipt it consumes. Host
scheduling noise may make values vary,
but identity, method, sample cardinality, percentile calculation, and
acceptance are deterministic and independently recomputable.

The hashed `benchmark_operation_plan_v1.json` freezes the schedule. After the
single provider start, the collector opens and verifies baseline `S0`. Each of
exactly `warmup_count` discarded rounds runs the full query plan against `S0`,
applies fixed one-document delta `D` to declared `S1`, resets to byte-identical
`S0`, performs a full rebuild of `S0`, then resets and verifies `S0`. Each of
exactly `sample_count` measured rounds first resets/verifies `S0`, then times
all queries in plan order. Even rounds time publish `D`, reset/verify `S0`, then
time a full rebuild; odd rounds time the full rebuild, reset/verify `S0`, then
time publish `D`. A final untimed reset follows each round. Resets are outside
operation timings but inside RSS/activity observation and never restart the
provider. Queries never observe `S1` or rebuilt mutable state. The plan binds
`S0`, `S1`, `D`, query order, counts, reset method, and expected hashes; any
schedule, state, or hash deviation is `not_evidence`.

#### 14.6.2 Sole collection command

After implementation, the only qualified collection entry point is:

```bash
SPIPE_SIMPLE_BIN=/absolute/admitted/simple \
SPIPE_STAGE4_PROVENANCE=/absolute/admitted/stage4-candidate.sdn \
node examples/05_stdlib/spipe/test/perf/measure_qualified_search.mjs \
  --profile examples/05_stdlib/spipe/test/fixture/wave4_search/qualified_search_profile_v1.json \
  --fixture examples/05_stdlib/spipe/test/fixture/wave4_search/qualified_search_50000_v1.json \
  --operation-plan examples/05_stdlib/spipe/test/fixture/wave4_search/benchmark_operation_plan_v1.json \
  --functional-receipt file:///absolute/admitted/wave4-functional-conformance-v1.json \
  --output build/test-artifacts/spipe-wave4/qualified-search-receipt-v1.json
```

The executable accepts no implicit binary, provenance, fixture, output, or
profile fallback. Paths must be absolute after canonicalization and may not be
symlinks. It first invokes the canonical Stage 4 provenance verifier and Wave 4
conformance admission used by the parity harness, then measures. The checked-in
profile freezes budgets and method; the large generated fixture may be
content-addressed, but its manifest/hash and deterministic generator are
tracked. The command exits nonzero and removes any temporary output when
admission or collection fails. Because no admitted Stage 4 executable exists
at this design freeze, W4-SRCH-09 remains `NOT EVIDENCE`; no seed or source-mode
run can satisfy it.

### 14.7 Unicode 17.0.0 table deliverable

`spipe-unicode-lex-v1` freezes UCD **17.0.0**, released 2025-09-09. It never
delegates semantics to the host JavaScript engine, locale, C library, ICU, or
compiler runtime. Before analyzer implementation begins, Wave 4 must check in:

```text
examples/05_stdlib/spipe/src/search/generated/unicode_17_0_0.js
src/lib/common/search/generated/unicode_17_0_0.spl
examples/05_stdlib/spipe/test/fixture/wave4_search/unicode_17_0_0_manifest.json
```

The manifest records UCD version, generator source hash/version, source-file
names and SHA-256 hashes, generated-file SHA-256 hashes, Unicode license, and
generation command. Required UCD inputs are `UnicodeData.txt`,
`DerivedCoreProperties.txt`, `PropList.txt`, `SpecialCasing.txt`,
`CaseFolding.txt` (proven unused for lowercase), `CompositionExclusions.txt`,
and `NormalizationTest.txt`. The implementation gate regenerates into a
temporary directory, compares every byte and declared hash, runs the complete
UCD normalization corpus plus cross-runtime scalar fixtures, and rejects a
dirty or engine-derived table. The manifest's actual generated hashes are
filled only by that reproducible generation; absence or a placeholder hash
blocks Wave 4 implementation acceptance.

Exact string analysis is: validate shortest-form UTF-8 and Unicode scalar
values; normalize to NFC 17.0.0; apply locale-independent Unicode 17.0.0
**Default Lowercase Conversion**, including unconditional and applicable
contextual `SpecialCasing.txt` mappings but excluding locale-tailored mappings;
then NFC-normalize the lowercase result once more before tokenization. This is
lowercasing, not default case folding. Keys, facets, tokens, and canonical JSON
strings use the resulting scalar sequence where their schema calls for
analyzed text.

### 14.8 Authorization-partitioned logical indexes

There is no global corpus-statistics snapshot containing differently visible
documents. `AuthorizationPort` first resolves a canonical `SearchScopeV1` from
principal, workspace/revision, policy version and digest, permitted project and
visibility partitions, and authorized field/facet set. Its
`scope_digest = sha256(canonicalJson(SearchScopeV1))` contains no secret token.
Only then may an adapter open or build a lexical snapshot.

```text
SearchScopeV1 {
  contract:"spipe-search-scope-v1", principal_uid, workspace_uid,
  revision_id, policy_version, policy_digest,
  project_uids:[sorted], visibility_partitions:[sorted],
  searchable_fields:[closed-order subset], facet_names:[UTF-8 sorted]
}
```

The logical-root object in Section 14.4 additionally contains
`scope_digest`. Its document set, `N`, every `df`, total/average field length,
postings, facets, snippets, explanations, and result counts are computed solely
from documents and fields authorized in that scope. Root, query receipt, cache
key, cursor, delta, publication receipt, and provider request/response all bind
the same scope digest. Scope mismatch is `unauthorized` before index/statistic
access; scope partitions never share pages, cursors, score explanations, or
mutable deltas even when their visible document sets happen to match.

Redaction removes the field before analysis and statistics; it is not an empty
field and cannot match, affect length/average/`df`, or appear in explanation.
A document with no searchable authorized fields may remain resolvable by the
SPipe identity tier when policy permits, but it is absent from lexical corpus
statistics and candidates. Facet authorization is checked before lookup.
Cross-scope golden fixtures prove that adding private documents or redacted
terms changes no public root, statistic, score, tie, count, cursor, cache entry,
or timing-visible error shape.

### 14.9 Canonical JSON byte profile

`spipe-canonical-json-v1` is the sole encoding used for logical roots, payload
hashes, receipts, and provider canonicality checks:

- bytes are valid shortest-form UTF-8 with no BOM;
- every string and object key is UCD-17.0.0 NFC; two input keys that normalize
  equal are a duplicate-key error before object construction;
- object keys sort by unsigned UTF-8 bytes; arrays retain schema order unless a
  field explicitly requires canonical sorting;
- values are only objects, arrays, strings, booleans, null, and schema-bounded
  signed integers; numbers use shortest base-10 digits, no leading zero,
  exponent, decimal point, plus sign, or `-0`;
- every integer must be within the receiving schema's bound and within signed
  64-bit range; protocol parsers also reject values not exactly representable
  by their implementation rather than round them;
- strings escape only quotation mark, reverse solidus, and U+0000–U+001F,
  using lowercase `\u00xx` for controls without a short JSON escape; all other
  scalars are emitted as UTF-8, never surrogate escapes;
- undefined, holes, duplicate fields, NaN, infinities, lone surrogates,
  comments, and trailing data are errors.

Hashed payload bytes contain no whitespace or trailing newline. A wire frame's
eight-byte lowercase-hex length counts payload bytes only, excluding the header.
Checked-in golden fixtures contain the source value, exact canonical byte
sequence (hex), and SHA-256 for empty/boundary/nested/Unicode cases and every
rejection class. JavaScript, Simple, fallback, DBFS, and process adapters must
match those bytes and hashes.

### 14.10 Normative checked BM25 evaluation

All quantities below are nonnegative checked integers. Conceptual
intermediates are signed i128. An implementation without i128 must prove before
each operation that its i64 result is identical; otherwise it returns
`score_overflow`. Division is integer truncation toward zero. No reassociation,
floating point, saturation, or intermediate public-milli rounding is allowed.

```text
S = 1_000_000; K1 = 1_200_000; B = 750_000; LN2 = 693_147
avg_scaled = checked_div(total_field_length * S, N)       # N > 0
ratio_scaled = checked_div(document_length * S * S, avg_scaled)
norm_scaled = (S - B) + checked_div(B * ratio_scaled, S)
denom_scaled = tf * S + checked_div(K1 * norm_scaled, S)
tf_scaled = checked_div(tf * (K1 + S) * S, denom_scaled)
idf_arg_scaled = S + checked_div((2*N - 2*df + 1) * S, 2*df + 1)
idf_scaled = fixed_ln(idf_arg_scaled)
unweighted = checked_div(idf_scaled * tf_scaled, S)
weighted = checked_div(unweighted * weight_milli, 1000)
internal_total = checked_sum(weighted in field order, then term UTF-8 order)
public_score_milli = checked_div(internal_total, 1000)
```

Terms absent from a field (`tf=0`) contribute zero without evaluating the
denominator. A term that is scored requires `N>0`, `0<=df<=N`,
`total_field_length>0`, and `avg_scaled>0`. Average length is exactly
`floor(total_field_length*S/N)`; missing fields contributed zero when the total
was built. Query terms are distinct and ordered by unsigned UTF-8 token bytes;
`qtf` is explanation-only.

`fixed_ln(x_scaled)` requires `x_scaled>0`. Repeated checked multiplication by
2 or truncating division by 2 produces exponent `e` and mantissa `m` in
`[S,2*S)`, with boundary values assigned to the lower inclusive interval.
Then `y=checked_div((m-S)*S,m+S)`. Evaluate in this exact order:

```text
y2 = y*y/S
sum = y
power = y
for denominator in 3,5,7,9,11,13:
    power = power*y2/S
    sum += power/denominator
result = 2*sum + e*LN2
```

Every multiplication/addition and the final range is checked. Golden vectors
cover `S-1`, `S`, `S+1`, `2*S-1`, `2*S`, range-reduction extremes, every
rounding boundary, zero/one corpus, `df=0/N`, and each overflow/error branch.

### 14.11 Closed provider protocol schemas

The protocol field is always the object `{major:1,minor:0}`; integer `1` is
invalid. All records below are closed: missing, extra, duplicate-normalized, or
wrongly typed fields fail the whole generation unless an initialization field
is explicitly listed in `optional_fields` for a compatible minor version.

```text
InitializeRequestV1 {
  request_id, operation:"initialize", protocol:{major,minor}, client:"spipe",
  required:{provider,analyzer,score,explanation,logical_index}, limits
}
InitializeResultV1 {
  request_id, operation:"initialize", ok:true, result:{protocol,provider,implementation_digest,
  provider_ids,analyzer_ids,score_ids,explanation_ids,logical_index_ids,
  capabilities,limits,optional_fields}
}
RequestV1 {
  request_id:RequestId, operation:closed-operation, protocol:{major:1,minor:0},
  provider_generation:ProviderGeneration, workspace:WorkspaceId,
  snapshot:SnapshotId, scope_digest:HashText,
  query_receipt:QueryReceiptV1|null,
  operation_receipt:OperationReceiptV1|null,
  deadline_ms:DeadlineMs, payload:closed-operation-payload
}
SuccessResponseV1 {
  request_id:RequestId, operation:closed-operation, ok:true, protocol,
  provider_generation:ProviderGeneration, workspace:WorkspaceId,
  snapshot:SnapshotId, scope_digest:HashText,
  query_receipt:QueryReceiptV1|null,
  operation_receipt:OperationReceiptV1|null, result:closed-operation-result
}
ErrorResponseV1 {
  request_id:RequestId, operation:closed-operation, ok:false, protocol,
  provider_generation:ProviderGeneration, workspace:WorkspaceId,
  snapshot:SnapshotId, scope_digest:HashText,
  query_receipt:QueryReceiptV1|null,
  operation_receipt:OperationReceiptV1|null,
  error:ProviderErrorV1
}
PreBindingErrorResponseV1 {
  request_id, operation, ok:false, protocol,
  error:ProviderErrorV1{code,message,retryable:false}
}
```

`PreBindingErrorResponseV1` is legal only for (a) `initialize` rejection or
(b) `handshake_required` after any syntactically valid, canonical, closed
operation request received before successful initialization. Case (b) echoes
only the decoded `request_id`, `operation`, and protocol and intentionally has
no `provider_generation`, workspace, snapshot, scope, or receipts because no
binding exists yet. A malformed length header, invalid UTF-8/JSON, noncanonical
JSON, unknown operation, or request from which those three fields cannot be
recovered closes the transport silently; it never fabricates a response.
Specifically, `invalid_utf8` and `frame_too_large` are local
`TransportDiagnosticV1` classes, not values of `ProviderErrorV1`.
Every post-initialization error uses `ErrorResponseV1` and echoes the exact
request bindings. The adapter deterministically creates and sends a non-null
`query_receipt` for `search` and `explain`; every bound success or error echoes
it. Other operations send and echo `query_receipt:null`. Requests always send
`operation_receipt:null`; successful or byte-identical replayed `index_apply`
and `index_publish` return their non-null signed receipt, while their errors and
all other responses return null. Thus only the explicitly pre-binding schema
may omit workspace/snapshot/scope/receipt binding fields. Any bound-error
mismatch quarantines the generation just like a mismatched success.

Initialization requires exact support for `spipe-search-provider/1.0`,
`spipe-unicode-lex-v1`, `bm25-fixed-v1`, `bm25-explain-v1`, and
`spipe-lexical-snapshot-v1`; negotiated capabilities explicitly include
`phrase:false`, `regex:false`, and `wildcard:false`. `rrf-fixed-v1` is
adapter-local SPipe composition state: it is neither required from the provider
nor accepted as an authoritative provider result. A provider may echo it only
inside non-authoritative diagnostic metadata declared optional; it never binds
or computes fusion.

Operation payload/result schemas are closed per the operation table in Section
4.3. Error responses cannot include `result`; success responses cannot include
`error`. Before initialization only `InitializeRequestV1` may execute; any
other syntactically valid closed operation request receives the pre-binding
`handshake_required` response defined above and has no side effects.
Correlation, generation, workspace, snapshot, scope, query receipt, capability, limit, and
logical-root mismatches quarantine the generation.

### 14.12 Closed operation payloads and results

Wire aliases are normative: `IdText` is NFC UTF-8, 1–128 bytes, without control
characters; `HashText` is lowercase `sha256:` plus 64 hex digits; `CursorText`
is null or an authenticated base64url value of at most 8,192 bytes; `Count` is
an integer in `[0,1_000_000]`; and arrays have the explicit maxima below. Every
payload and result is a closed object.

| Operation | Exact request `payload` | Exact success `result` |
|---|---|---|
| `index_open` | `{mode:"open"|"create", logical_root:HashText|null}`; null is legal only for `create` | `{logical_root:HashText, document_count:Count, state:"opened"|"created"}` |
| `index_apply` | `{operation_id:IdText, payload_hash:HashText, base_logical_root:HashText, operations:[IndexOperationV1; max 1000]}` | `{status:"applied"|"no_op", base_logical_root:HashText, candidate_uid:IdText, candidate_logical_root:HashText, candidate_expires_at_ms:UnixMillis, added:Count, replaced:Count, deleted:Count}` |
| `index_publish` | `{operation_id:IdText, payload_hash:HashText, action:"publish"|"abort", candidate_uid:IdText, expected_base_logical_root:HashText, candidate_logical_root:HashText}` | `{status:"published"|"aborted"|"stale_base", previous_logical_root:HashText, logical_root:HashText, candidate_uid:IdText}`; `stale_base` is a terminal success carrying that request's signed `OperationReceiptV1` and never mutates the current root |
| `search` | `{query_text:string<=4096 UTF-8 bytes, filters:[EqualityFilterV1; max 32], limit:integer[1,1000], cursor:CursorText, explain:boolean}` | `{logical_root:HashText, hits:[SearchHitV1; max limit], next_cursor:CursorText, exhausted:boolean}` |
| `explain` | `{document_id:IdText, query_text:string<=4096 bytes, filters:[EqualityFilterV1; max 32]}` | `{logical_root:HashText, document_id:IdText, explanation:SearchExplanationV1}` |
| `duplicate_candidates` | `{document_ids:[IdText; max 1000], limit_per_document:integer[1,100], cursor:CursorText}` | no Wave 4 success schema; capability is false and the bound response is `unsupported_capability` |
| `symbols_snapshot` | `{project_uid:IdText, revision:IdText, limit:integer[1,1000], cursor:CursorText}` | no Wave 4 success schema; capability is false and the bound response is `unsupported_capability` |
| `stats` | `{logical_root:HashText}` | `{logical_root:HashText, document_count:Count, field_stats:[FieldStatsV1; exactly scope searchable-field count], index_bytes:integer[0,9007199254740991], cache_bytes:integer[0,9007199254740991], peak_rss_bytes:integer[0,9007199254740991]}` |
| `cancel` | `{target_request_id:IdText}` | `{target_request_id:IdText, status:"cancelled"|"already_complete"}`; an unknown target is the bound error `cancel_target_not_found`, never a success |
| `shutdown` | `{reason:"normal"|"fallback"|"host_shutdown"}` | `{status:"closing"}` |

For `index_apply` and `index_publish`, `payload_hash` is non-circular. Remove
exactly the top-level `payload_hash` field from the otherwise complete closed
operation payload, canonicalize the remaining object, and hash:

```text
payload_hash = "sha256:" + sha256(
  domain || u64be(canonical_payload_byte_length) || canonical_payload_bytes)
apply domain   = "SPKC-INDEX-APPLY-PAYLOAD-V1\0"
publish domain = "SPKC-INDEX-PUBLISH-PAYLOAD-V1\0"
```

No nested field, operation ID, or empty array is omitted. The transmitted
`payload_hash` must equal this value before replay lookup or mutation.

`IndexOperationV1` is exactly one of:

```text
{kind:"add", document_id:IdText, before_revision:null, before_hash:null,
 after:ScopedSearchDocumentV1}
{kind:"replace", document_id:IdText, before_revision:IdText,
 before_hash:HashText, after:ScopedSearchDocumentV1}
{kind:"delete", document_id:IdText,
 before_revision:IdText|null, before_hash:HashText|null, after:null}
```

The two delete precondition fields form one closed tagged choice. Non-null /
non-null asserts that the document is present at `base_logical_root` with that
exact revision and scoped-document hash; an exact match deletes it, while an
absent or different document returns `precondition_conflict`. Null / null
asserts expected absence: an absent base document is a deterministic no-op,
while a present base document returns `precondition_conflict`. Mixed null and
non-null pairs are `invalid_request` and are rejected before replay lookup,
candidate creation, or receipt issuance. Preconditions are evaluated only
against the immutable base root, never against earlier operations in the same
delta.

An absence-delete no-op contributes zero to `deleted` and does not change the
candidate logical root. If every operation is a no-op, `index_apply` still
durably creates its deterministic candidate, returns `status:"no_op"`, and
issues an `OperationReceiptV1` with `outcome:"no_op"`; later publish/abort uses
the ordinary lifecycle. The null fields and `after:null` remain present in the
canonical payload and therefore affect `payload_hash`. Identical replay returns
the originally stored `no_op` envelope and receipt byte-for-byte. It neither
re-evaluates absence nor issues a new receipt.

Operations sort by unsigned UTF-8 `(document_id,kind)` and document IDs are
unique across the delta. `EqualityFilterV1` is exactly
`{name:IdText,values:[string;1..64]}`; names are unique/sorted and values are
NFC, unique, and unsigned-UTF-8 sorted. Different filter records are ANDed; a
record matches when its named facet equals any one of that record's values.
An analyzed document is a lexical candidate when at least one distinct query
term occurs; terms affect score but are not implicit AND predicates. Empty
analyzed query text is legal only when at least one filter exists and yields
score zero with ID ties.

`SearchHitV1` is exactly `{document_id:IdText,score_milli:WireInteger,
source_rank:integer[1,1000],matched_fields:[closed field names;max 5],
explanation:SearchExplanationV1|null}`; explanation is non-null iff requested.
`FieldStatsV1` is exactly `{field:closed field name,N:Count,
total_length:WireInteger,average_length_scaled:WireInteger}` in closed field
order. Search cursors bind provider generation, workspace, snapshot, scope,
logical root, query receipt, query bytes, filters, limit, explain flag, and next
rank; any mismatch is `stale_cursor`. Pagination returns each authorized hit at
most once and never crosses a snapshot or provider generation.

Wave 4 advertises only `index_delta`, `lexical`, `explain`, `stats`, `cancel`,
and `shutdown`; it explicitly advertises `phrase:false`, `regex:false`,
`wildcard:false`, `duplicate:false`, `symbols:false`, and `semantic:false`.
Deferred operations remain in the closed vocabulary so callers receive a
bound deterministic error, but no Wave 4 provider may return their success.

### 14.13 Wire integer contract

Every JSON numeric integer is in the inclusive JavaScript-safe range
`[-9007199254740991,9007199254740991]` and also satisfies its narrower schema
bound. Parsers reject `9007199254740992`, `-9007199254740992`, i64 extrema,
rounding, or an implementation-specific bigint JSON extension. Counters,
lengths, ranks, limits, versions, deadlines, scores, and frame-adjacent metadata
are nonnegative unless their schema explicitly states otherwise.

Checked conceptual i128 BM25 intermediates in `bm25-explain-v1` are encoded as
strings, never JSON numbers, using `I128Decimal = /^(0|-?[1-9][0-9]{0,38})$/`
and the inclusive mathematical bounds
`-170141183460469231731687303715884105728` through
`170141183460469231731687303715884105727`. `-0`, plus signs, leading zeros,
whitespace, exponent notation, out-of-range 39-digit values, and values used in
a field not declared `I128Decimal` are rejected. Explanation schema marks each
intermediate as either safe `WireInteger` or `I128Decimal`; implementations
must not choose dynamically between number and string for the same field.

### 14.14 Closed explanation records

`bm25-explain-v1` uses only the following closed records. `WireInteger` is the
safe JSON integer from Section 14.13; every arithmetic intermediate declared
`I128Decimal` is always a decimal string, even when its value would fit safely.

```text
SearchExplanationV1 {
  contract:"bm25-explain-v1", analyzer:"spipe-unicode-lex-v1",
  score_contract:"bm25-fixed-v1", logical_index:"spipe-lexical-snapshot-v1",
  scope_digest:HashText, logical_root:HashText, document_id:IdText,
  fields:[FieldExplanationV1; 0..authorized-field-count],
  internal_total:I128Decimal, public_score_milli:WireInteger,
  tie_key_utf8_hex:string[2..256 lowercase even hex]
}
FieldExplanationV1 {
  field:closed-field-name, N:WireInteger, total_length:WireInteger,
  average_length_scaled:I128Decimal,
  document_length:WireInteger, weight_milli:WireInteger,
  terms:[TermContributionV1; 0..128], field_total:I128Decimal
}
TermContributionV1 {
  kind:"absent", term:string[1..4096 UTF-8 bytes],
  qtf:WireInteger[1,128], df:WireInteger, tf:0,
  idf_argument_scaled:null, idf_scaled:null, length_ratio_scaled:null,
  norm_scaled:null, denominator_scaled:null, tf_scaled:null,
  unweighted:"0", weighted:"0"
} | {
  kind:"scored", term:string[1..4096 UTF-8 bytes],
  qtf:WireInteger[1,128], df:WireInteger, tf:WireInteger[1,max-field-length],
  idf_argument_scaled:I128Decimal, idf_scaled:I128Decimal,
  length_ratio_scaled:I128Decimal, norm_scaled:I128Decimal,
  denominator_scaled:I128Decimal, tf_scaled:I128Decimal,
  unweighted:I128Decimal, weighted:I128Decimal
}
```

Fields occur once in canonical authorized-field order; absent/redacted fields
do not occur. Terms occur once in ascending unsigned UTF-8 bytes, including
zero-contribution terms only when the query term is absent from this field.
Each term's `df` must not exceed its field's `N`. Bounds are the corresponding
query/document/statistic bounds. `qtf` is the exact count of that normalized
term in the pre-deduplicated analyzed query and never changes scoring. An
absent contribution requires the exact zeros/nulls above and evaluates no IDF,
length ratio, normalization, denominator, or division. A scored contribution
requires every intermediate. Recompute every scored term using
Section 14.10, checked-sum terms into `field_total`, checked-sum fields into
`internal_total`, convert once into `public_score_milli`, and compare the tie
key with the UTF-8 hex of `document_id`. Any missing, extra, reordered,
nonrecomputable, unauthorized, or over-limit explanation quarantines the
provider generation.

### 14.15 Canonical versus scoped documents

`SearchDocumentV1` is the compiler-owned, authorization-neutral projection and
always contains exactly the five closed fields. It is never sent wholesale to
a provider for a narrower caller. After `AuthorizationPort` resolves
`SearchScopeV1`, the coordinator derives:

```text
ScopedSearchDocumentV1 {
  document_id, revision,
  fields:[authorized subset in canonical field order],
  facets:[authorized subset sorted by UTF-8 name,value],
  visibility_digest, scoped_content_hash, scope_digest
}
```

`ScopedFieldV1` is exactly `{name:closed-field-name,value:NFC-string}` and may
occur at most once. `ScopedFacetV1` is exactly `{name:IdText,value:NFC-string}`;
duplicate `(name,value)` pairs are rejected. Both arrays are closed and sorted
as stated. `scoped_content_hash` is SHA-256 of the canonical scoped record with
that one field omitted; it therefore commits only authorized content and cannot
be compared with the global `SearchDocumentV1.content_hash`.

An empty authorized field subset removes the document from the lexical corpus.
`FieldStatsV1` and explanation arrays contain only authorized fields, in their
relative canonical order; absent fields have no zero placeholder and do not
affect roots, `N`, `df`, total length, average length, postings, or caches. The
five-field global projection and each scoped projection have different schemas
and cannot share hashes.

An adapter declares its supported scope partition modes in initialization. A
DBFS adapter that cannot create independently authorized statistics for the
requested `scope_digest` returns bound `unsupported_scope` before reading any
postings/statistics; it cannot reuse a broader DBFS index and filter afterward.
Conformance includes cross-scope Simple, JS, and applicable DBFS roots and
statistics.

Every provider-bound `index_open`, `IndexOperationV1.after`, replay payload,
candidate object, logical root, and clean-build corpus uses
`ScopedSearchDocumentV1` exclusively. `SearchDocumentV1` cannot cross the
provider boundary. `stats.field_stats` has exactly the number and relative
canonical order of `SearchScopeV1.searchable_fields`; a missing, extra,
redacted, reordered, or broader field is `binding_mismatch` and quarantines the
generation.

### 14.16 Envelope scalar and receipt schemas

All common fields use exact aliases:

```text
RequestId = IdText
ProviderGeneration = "pg-" + 32 lowercase hex digits
WorkspaceId = canonical WS- UID, at most 128 bytes
SnapshotId = canonical spks1- snapshot UID, at most 128 bytes
DeadlineMs = WireInteger in [1,30000]
QueryReceiptId = null | "qr-" + 64 lowercase hex digits
OperationReceiptId = null | "or-" + 64 lowercase hex digits
CandidateExpiryReceiptId = "cer-" + 64 lowercase hex digits
KeyId = "ed25519:" + 64 lowercase hex digits
UnixMillis = WireInteger in [0,9007199254740991]
```

Deadlines are relative durations measured from receipt by an adapter monotonic
clock; Unix milliseconds appear only in signed audit/expiry records and never
drive an in-flight timeout.

```text
QueryReceiptV1 {
  schema:"spipe-query-receipt-v1", receipt_id:QueryReceiptId(non-null),
  key_id:KeyId, authority_id:IdText, authority_generation:WireInteger,
  request_id:RequestId, operation:"search"|"explain",
  provider_generation:ProviderGeneration, workspace:WorkspaceId,
  snapshot:SnapshotId, scope_digest:HashText, logical_root:HashText,
  query_hash:HashText, issued_at_ms:UnixMillis, expires_at_ms:UnixMillis,
  policy_version:WireInteger, policy_digest:HashText,
  revocation_generation:WireInteger,
  signature:string[86 base64url Ed25519]
}
OperationReceiptV1 {
  schema:"spipe-operation-receipt-v1", receipt_id:OperationReceiptId(non-null),
  key_id:KeyId, authority_id:IdText, authority_generation:WireInteger,
  operation_id:IdText,
  operation:"index_apply"|"index_publish",
  provider_generation:ProviderGeneration, workspace:WorkspaceId,
  snapshot:SnapshotId, scope_digest:HashText, base_logical_root:HashText,
  result_logical_root:HashText, candidate_uid:IdText|null,
  payload_hash:HashText,
  outcome:"applied"|"no_op"|"published"|"aborted"|"stale_base",
  issued_at_ms:UnixMillis, expires_at_ms:UnixMillis,
  policy_version:WireInteger, policy_digest:HashText,
  revocation_generation:WireInteger,
  signature:string[86 base64url Ed25519]
}
CandidateExpiryReceiptV1 {
  schema:"spipe-candidate-expiry-receipt-v1",
  receipt_id:CandidateExpiryReceiptId, key_id:KeyId,
  authority_id:IdText, authority_generation:WireInteger,
  candidate_uid:IdText, workspace:WorkspaceId, snapshot:SnapshotId,
  scope_digest:HashText, base_logical_root:HashText,
  candidate_logical_root:HashText, apply_operation_id:IdText,
  apply_receipt_id:OperationReceiptId(non-null),
  candidate_expires_at_ms:UnixMillis, expired_at_ms:UnixMillis,
  policy_version:WireInteger, policy_digest:HashText,
  revocation_generation:WireInteger,
  outcome:"expired", signature:string[86 base64url Ed25519]
}
DurableTerminalErrorV1 {
  schema:"spipe-durable-terminal-error-v1",
  workspace:WorkspaceId, snapshot:SnapshotId, scope_digest:HashText,
  operation:"index_publish", operation_id:IdText, payload_hash:HashText,
  candidate_uid:IdText,
  observed_terminal_state:"published"|"aborted"|"expired"|"stale_base",
  observed_terminal_receipt_kind:"operation"|"candidate_expiry",
  observed_terminal_receipt_id:OperationReceiptId(non-null)|CandidateExpiryReceiptId,
  response:ErrorResponseV1, response_hash:HashText,
  recorded_at_ms:UnixMillis
}
```

The unsigned record is the closed receipt with exactly `receipt_id` and
`signature` omitted. Signing input is `domain || u64be(byte_length) ||
canonicalJson(unsigned_record)`, where domain is
`SPKC-QUERY-RECEIPT-V1\0` or `SPKC-OPERATION-RECEIPT-V1\0`. Receipt ID is
SHA-256 of that input and Ed25519 signs exactly that same input. Keys come only
from a separately configured
`ReceiptAuthorityPort`; `key_id` is the SHA-256 fingerprint of the admitted
public key, never provider self-assertion. Verification checks signature,
authority, expiry, revocation generation, policy, scope/root/request bindings,
and canonical bytes before use.

`CandidateExpiryReceiptV1` uses the same construction with domain
`SPKC-CANDIDATE-EXPIRY-RECEIPT-V1\0`. Its unsigned record omits exactly
`receipt_id` and `signature`, so neither value is inside its own canonical
preimage. `authority_id` identifies the admitted `CandidateAuthorityPort`,
`authority_generation` binds its durable scheduler epoch, policy fields bind
the authorization policy that admitted the expiry, and
`expired_at_ms >= candidate_expires_at_ms`. Verification additionally binds
every candidate/apply field above. The authority fsyncs the receipt and
terminal candidate record as specified by the single-commit rule in Section
14.17; restart reloads and verifies both, and byte-identical internal expiry
replay returns the same receipt bytes.

On the provider boundary, envelope `query_receipt` is the complete signed
`QueryReceiptV1` object or null and `operation_receipt` is the complete signed
`OperationReceiptV1` object or null—never a bare receipt ID. The `*ReceiptId`
aliases name only the nested `receipt_id` fields. Echo validation is byte-exact.

The durable replay key is `(workspace,snapshot,scope_digest,operation,
operation_id)`. Its payload hash, exact canonical success envelope, and verified
receipt are fsynced before reply and reloaded/reverified after restart.
Identical replay returns those same bytes with the original `applied`, `no_op`,
`published`, `aborted`, or `stale_base` status and matching receipt outcome;
there is no replay-only status or outcome;
changed payload is `operation_conflict`; expired/revoked receipt makes recovery
fail closed and requires an authorized audit/rebuild rather than re-execution.
`DurableTerminalErrorV1` has the same replay key, and its nested response must
bind that request and have `operation_receipt:null`. `response_hash` commits the
exact canonical response bytes. It records only the winner receipt's kind/ID,
never embeds or returns the winner receipt. Identical loser replay returns the
stored response bytes; a payload mismatch is `operation_conflict`.

### 14.17 Candidate publication lifecycle

`index_apply` creates a candidate but never changes the current root. Its unique
apply `operation_id` produces `{candidate_uid,candidate_logical_root,
candidate_expires_at_ms}` in the result and signed operation receipt. Candidate
UID is exactly `"cand-" + sha256(domain || u64be(length) || bytes)`, where
domain is `SPKC-CANDIDATE-UID-V1\0` and bytes are canonical JSON of the closed
record `{workspace,snapshot,scope_digest,base_logical_root,
candidate_logical_root,apply_payload_hash}` (keys canonicalize normally).
The prefix is ASCII and is not part of the hash preimage. No separator,
concatenation shorthand, provider-local ID, or receipt field is permitted.
Multiple candidates from one base may coexist.

`CandidateRecordV1.state` is closed to `staged`, `published`, `aborted`,
`expired`, or `stale_base`. Only `staged` may transition, exactly once, to one
of the four terminal states. Its closed fields bind candidate UID, apply
operation ID/receipt ID, workspace/snapshot/scope, base/candidate roots, payload
hash, created/expiry Unix milliseconds, state, terminal operation ID, terminal
receipt kind (`operation` or `candidate_expiry`), terminal receipt ID, and
terminal timestamp. For `staged`, all four terminal fields are null. For
`published`, `aborted`, or `stale_base`, terminal operation ID is non-null,
receipt kind is `operation`, and receipt ID/timestamp are non-null. For
`expired`, terminal operation ID is null, receipt kind is `candidate_expiry`,
and receipt ID/timestamp are non-null. No other null/discriminator combination
is legal.
Published/aborted/stale-base transitions bind their request's
`OperationReceiptV1`; only authority-owned expiry binds a
`CandidateExpiryReceiptV1`. `OperationReceiptV1` remains request-owned: apply
produces `applied` or `no_op`, successful publish produces `published`, abort
produces `aborted`, and a publish request that itself wins the candidate CAS
but finds a stale current root may durably record `stale_base`.

`index_publish` uses a distinct publish `operation_id` and payload
`{action:"publish"|"abort", candidate_uid, expected_base_logical_root,
candidate_logical_root}`. Publish verifies the durable candidate and performs
one parent-authoritative current-root CAS. The winner returns `published`; a
request that claims its own still-staged candidate after another candidate has
advanced the root terminalizes its candidate as `stale_base` and returns the
typed successful `stale_base` result with its own signed operation receipt and
no current-root mutation.
`abort` durably marks an unpublished candidate aborted and returns `aborted`;
replay is idempotent. Expiry durably transitions an unpublished candidate to
`expired`. Aborted, expired, losing, corrupt, or wrong-scope candidates can
never publish and are reclaimed only after their replay/audit retention period.

`PublicationRecordV1` is the closed durable metadata record
`{schema:"spipe-publication-v1",operation_id,payload_hash,candidate_uid,
previous_logical_root,result_logical_root,operation_receipt_id,published_at_ms}`.
For `published`, one parent-authoritative transaction evaluates both the
candidate-state and expected-current-root predicates and, if both hold,
atomically commits (1) the new current-root pointer, (2) terminal
`CandidateRecordV1`, (3) exact signed `OperationReceiptV1`, and (4)
`PublicationRecordV1`. The transaction is the sole publish linearization point.
For `stale_base` and `aborted`, the same transaction facility atomically commits
the terminal candidate plus its signed receipt, but no current-root pointer or
publication record. Candidate document/statistic objects were already durable
and immutable before any terminal transaction.

Candidate time and transitions are owned by the parent adapter's
`CandidateAuthorityPort`, using its monotonic scheduler plus signed Unix audit
time; providers cannot self-expire or revive candidates. For every terminal
transition, the authority first prepares and signs the matching receipt in
memory, then performs the applicable atomic transaction above. There is no
visible intermediate state containing only a root pointer, terminal candidate,
receipt, or publication record subset; the transaction is fsynced before any
response.
Expiry uses the separate authority receipt above and has no fabricated client
operation identity.
Abort versus publish versus expiry races have one candidate-state CAS winner.
A request that loses the candidate-state CAS returns its own request-bound `ErrorResponseV1`
with `operation_receipt:null` and the exact terminal error (`candidate_expired`,
`candidate_aborted`, or `stale_base`); it never receives or replays the winner's
receipt. Before responding, the adapter atomically writes and fsyncs a closed
`DurableTerminalErrorV1` under the losing request's replay key. An identical
replay after completion or restart returns its exact stored bound error bytes.
Only byte-identical replay of the winning request may return its winning
`OperationReceiptV1`; expiry receipt replay is internal to the authority/audit
API. Restart loads and verifies candidate plus the correctly discriminated
receipt before permitting replay or publication. Corruption returns
`snapshot_corrupt`/`fatal_provider_error` and quarantines without synthesizing
a new outcome.

#### 14.17.1 Normative closure wire vectors

`provider_protocol_vectors.json` contains these records as exact UTF-8 bytes,
not merely structural examples. Canonical serialization and framing assertions
are:

| Vector | Exact canonical payload | Payload bytes / frame header / SHA-256 |
|---|---|---|
| `preinit_search_handshake_required` | `{"error":{"code":"handshake_required","message":"initialize first","retryable":false},"ok":false,"operation":"search","protocol":{"major":1,"minor":0},"request_id":"req-pre-1"}` | `176` / `000000b0` / `dc4f4f42bbe0ef560712e07f5fccac703c6539535b1fa5f863454b5ed55a58d3` |
| `cancel_unknown_bound_error` | `{"error":{"code":"cancel_target_not_found","message":"target request never existed in this generation","retryable":false},"ok":false,"operation":"cancel","operation_receipt":null,"protocol":{"major":1,"minor":0},"provider_generation":"pg-00000000000000000000000000000000","query_receipt":null,"request_id":"req-cancel-1","scope_digest":"sha256:0000000000000000000000000000000000000000000000000000000000000000","snapshot":"spks1-test","workspace":"WS-TEST"}` | `456` / `000001c8` / `4c70646ba965bd9f3c4524ed322ef1d8e0cd3c1d9a74c250b0359dfa11054fc8` |

Payload/identity vectors use actual NUL domain terminators:

| Vector | Exact canonical preimage record | Bytes / domain-preimage SHA-256 |
|---|---|---|
| `apply_payload_without_hash` | `{"base_logical_root":"sha256:0000000000000000000000000000000000000000000000000000000000000000","operation_id":"apply-1","operations":[]}` | `136` / `53eac50845e9d3c9014580d3136062cb03e36c7863f947124e63bb674e38308f` |
| `absence_delete_payload_without_hash` | `{"base_logical_root":"sha256:0000000000000000000000000000000000000000000000000000000000000000","operation_id":"delete-absence-1","operations":[{"after":null,"before_hash":null,"before_revision":null,"document_id":"doc-missing","kind":"delete"}]}` | `245` / `9f3366f906834cadde2ea4b02494f47f8dc80f37418729785841e7209d1d9f08` |
| `publish_payload_without_hash` | `{"action":"publish","candidate_logical_root":"sha256:1111111111111111111111111111111111111111111111111111111111111111","candidate_uid":"cand-test","expected_base_logical_root":"sha256:0000000000000000000000000000000000000000000000000000000000000000","operation_id":"publish-1"}` | `277` / `cf61ac4db6bd270c671a5dd63e47bcc990714d2390cfe14acbfe6131e9042eee` |
| `candidate_uid_record` | `{"apply_payload_hash":"sha256:53eac50845e9d3c9014580d3136062cb03e36c7863f947124e63bb674e38308f","base_logical_root":"sha256:0000000000000000000000000000000000000000000000000000000000000000","candidate_logical_root":"sha256:1111111111111111111111111111111111111111111111111111111111111111","scope_digest":"sha256:3333333333333333333333333333333333333333333333333333333333333333","snapshot":"spks1-test","workspace":"WS-TEST"}` | `424` / `4adcb8c9713f37d79044d0130b7117f7a4c8d1b3e57a255a9a34be40ffbdb191`; expected UID `cand-4adcb8c9713f37d79044d0130b7117f7a4c8d1b3e57a255a9a34be40ffbdb191` |

The payload hashes use their respective apply/publish domains from Section
14.12; the candidate vector uses `SPKC-CANDIDATE-UID-V1\0`. Including the
transmitted `payload_hash` in its own preimage, removing the empty operations
array, omitting either null from the absence-delete record, mixing a null with
a non-null delete precondition, hashing the `cand-` prefix, changing the domain
terminator, or raw field concatenation is a rejection vector. The absence
fixture runs against both an absent and a present base document: only the
absent case returns the stored `no_op` envelope/receipt and unchanged root;
the present case returns `precondition_conflict` with null receipt and creates
no candidate.

The expiry vector's exact unsigned canonical record is:

```json
{"apply_operation_id":"apply-1","apply_receipt_id":"or-0000000000000000000000000000000000000000000000000000000000000000","authority_generation":7,"authority_id":"candidate-authority-test","base_logical_root":"sha256:0000000000000000000000000000000000000000000000000000000000000000","candidate_expires_at_ms":1000,"candidate_logical_root":"sha256:1111111111111111111111111111111111111111111111111111111111111111","candidate_uid":"cand-test","expired_at_ms":1001,"key_id":"ed25519:2222222222222222222222222222222222222222222222222222222222222222","outcome":"expired","policy_digest":"sha256:4444444444444444444444444444444444444444444444444444444444444444","policy_version":5,"revocation_generation":3,"schema":"spipe-candidate-expiry-receipt-v1","scope_digest":"sha256:3333333333333333333333333333333333333333333333333333333333333333","snapshot":"spks1-test","workspace":"WS-TEST"}
```

It is exactly 880 bytes. With domain
`SPKC-CANDIDATE-EXPIRY-RECEIPT-V1\0` and its eight-byte big-endian length, the
receipt preimage SHA-256—and therefore suffix of `receipt_id`—is
`5bf2e3a55ccfba6130ed059cb4c063c0db39b0f4fbf4845953cabbdf06c268cc`.
The former 771-byte record without the now-required policy fields has the
correct NUL-domain preimage SHA-256
`f13c7cce500d3d29b81c75880195f8ffcba4006ad16313a69ac1a43294731d40`
and is a closed-schema rejection vector, not a valid expiry receipt.
The fixture supplies the deterministic test key/signature and asserts that
adding `receipt_id` or `signature` to the preimage changes verification to
failure. Mutations of authority ID/generation, either time, candidate/apply
binding, receipt kind, or durable replay bytes also fail.

### 14.18 Transport diagnostics and bound provider errors

`TransportDiagnosticV1` is local, payload-free evidence. Its closed code set is
`invalid_utf8 | frame_too_large`; it may retain bounded numeric byte/count
metrics but no request payload, message/details copied from input, request ID,
operation, provider generation, workspace, snapshot, scope, or receipt. It is
never serialized as a provider response. A pre-binding occurrence records the
local diagnostic and closes silently.

`ProviderErrorV1` is the closed `{code,message,retryable}` object carried only
by the applicable `ErrorResponseV1` or defined `PreBindingErrorResponseV1`.
Its code set is:

| Code | Operations | Exact condition |
|---|---|---|
| `invalid_request` | all | closed-schema/type/null/order violation |
| `noncanonical_json` | all | canonical byte-profile violation |
| `limit_exceeded` | all | another declared structural/resource bound is exceeded |
| `protocol_unsupported` | initialize/pre-binding | protocol major/minor cannot be negotiated |
| `handshake_required` | all except initialize | operation received before healthy initialization |
| `incompatible_contract` | initialize/all | analyzer/score/explanation/root identity mismatch |
| `binding_mismatch` | bound operations | generation/workspace/snapshot/scope/root/receipt/field binding differs |
| `unsupported_capability` | search/deferred operations | known operation/query feature is not negotiated |
| `unsupported_scope` | index_open/apply/search/explain/stats | adapter cannot isolate authorized statistics before access |
| `snapshot_not_found` | index_open/read operations | named snapshot/root is absent |
| `snapshot_conflict` | index_open/apply/publish | requested snapshot conflicts with the bound workspace generation |
| `snapshot_corrupt` | index_open/read/recovery | persisted snapshot bytes/hash/schema fail verification |
| `invalid_corpus_n` | apply/search/explain/stats | `N` is zero where scoring is required or inconsistent with live corpus |
| `invalid_document_frequency` | apply/search/explain/stats | `df<0`, `df>N`, or postings disagree with `df` |
| `invalid_average_length` | apply/search/explain/stats | total/average is nonpositive or not exact |
| `invalid_denominator` | search/explain | BM25/log division denominator is nonpositive |
| `invalid_parallel_arrays` | apply/search/explain/stats | fields/statistics/postings/terms/weights differ in length/order |
| `invalid_logarithm_input` | search/explain | fixed-ln input is nonpositive or range reduction misses `[S,2S)` |
| `score_overflow` | apply/search/explain/stats | checked arithmetic/conversion exceeds declared type |
| `unauthorized` | all scoped operations | scope/field/facet/root access denied before index access |
| `stale_cursor` | search/deferred paged operations | cursor binding/generation/root/query mismatch or expiry |
| `stale_base` | index_apply; index_publish only after losing its candidate-state CAS to an already terminal published/stale candidate | apply base is no longer current, or the request observes that terminal state; a still-staged candidate whose base lost the current-root CAS uses the signed `status:"stale_base"` success instead |
| `operation_conflict` | index_apply/index_publish | replay key reused with a different payload hash |
| `candidate_missing` | index_publish | candidate absent or belongs to another context |
| `candidate_expired` | index_publish | candidate expired before publication |
| `candidate_aborted` | index_publish | candidate was durably aborted |
| `deadline_exceeded` | all bound operations | monotonic deadline crossed according to Section 14.19 |
| `cancelled` | target operation | accepted cancellation won before target commit admission |
| `cancel_target_not_found` | cancel | target request never existed in this generation |
| `semantic_unavailable` | optional future semantic source | source failed/was denied; lexical generation remains valid |
| `semantic_mismatch` | optional future semantic source | model/snapshot/scope/result binding differs; semantic source quarantined |
| `provider_unavailable` | all | generation/fallback cannot serve the same logical root |
| `internal_error` | all | bounded recoverable implementation failure with no publication |
| `fatal_provider_error` | all | invariant/storage corruption requires generation quarantine/close |

Codes do not collapse into a generic score error. Each failure publishes no
page/root unless its operation's lifecycle explicitly says a prior durable
candidate exists.

### 14.19 Cancellation, deadlines, and shutdown

Each request-control owner has an atomic state
`pending -> commit_admitted -> completed` or
`pending -> cancelled -> completed`. `cancel` linearizes by CAS from pending to
cancelled; `already_complete` means the target was already commit-admitted or
completed. A target that never existed in this provider generation returns the
bound `cancel_target_not_found` error with `retryable:false`,
`query_receipt:null`, and `operation_receipt:null`; `not_found` is not a success
status. An accepted cancellation guarantees no result page, candidate, or
current-root publication occurs afterward. `try_commit_admission` arbitrates
only cancel/deadline eligibility and creates no search-state truth. For
`index_apply`, semantic mutation linearization is
durable candidate creation; for every terminal `index_publish` outcome
(`published`, `stale_base`, or `aborted`), linearization is the single atomic
terminal transaction in Section 14.17—not an earlier candidate check or a bare
root-pointer CAS;
for reads, immutable snapshot pin plus completed bounded result construction.

The decoder samples a monotonic clock when it accepts the first frame-header
byte. After the typed envelope supplies `deadline_ms`, the request-control owner
computes the checked absolute deadline from that recorded header timestamp,
accepting only the inclusive range 1..30,000 milliseconds. Ingress framing,
UTF-8/JSON/schema work, normalization, hashing, execution, and response
construction therefore consume one semantic budget. Expiry before a complete
trusted binding closes silently; expiry after binding but before
`try_commit_admission` returns `deadline_exceeded`. Cancellation/deadline
winning commit-admission arbitration prevents the following mutation
transaction and produces no new candidate or terminal receipt.
The atomic ordering is binary: cancellation/deadline ordered before the
commit-admission permit prevents commit work; once the permit is issued,
cancellation/deadline reports `already_complete` and cannot relabel the later
durable result. The permit itself is not the linearization point. The durable
candidate-creation or combined terminal transaction is indivisible; the
adapter returns or replays its signed result and no observer can order inside
it. Workers check cancel/deadline at bounded work intervals and call
`try_commit_admission` immediately before entering every durable mutation
linearization transaction.

`shutdown` first linearizes `healthy -> closed-to-new-work`, rejects new work,
and drains commit-admitted operations. It cancels pending operations, waits
up to its configured monotonic drain deadline, then kills the owned process
group. A publish not commit-admitted before shutdown/cancel cannot publish
during or after drain. Replay storage and the current-root CAS determine restart state;
process exit timing never does.

### 14.20 Closed initialization negotiation

Initialization nested records are exact:

```text
RequiredContractsV1 {
  provider:"spipe-search-provider/1.0",
  analyzer:"spipe-unicode-lex-v1", score:"bm25-fixed-v1",
  explanation:"bm25-explain-v1",
  logical_index:"spipe-lexical-snapshot-v1"
}
ProviderCapabilitiesV1 {
  index_delta:true, lexical:true, explain:true, stats:true, cancel:true,
  shutdown:true, phrase:false, regex:false, wildcard:false,
  duplicate:false, symbols:false, semantic:false,
  scope_partition:"independent"|"unsupported"
}
ProviderLimitsV1 {
  max_frame_bytes:1048576, max_query_bytes:4096, max_query_tokens:128,
  max_filters:32, max_values_per_filter:64, max_hits:1000,
  max_delta_documents:1000, max_fields_per_document:5,
  max_field_value_bytes:1048576, max_explanation_terms:128,
  max_explanation_fields:5, max_explanation_bytes_per_hit:65536,
  max_page_bytes:524288, min_deadline_ms:1, max_deadline_ms:30000
}
InitializeRequiredIdsV1 {
  provider_ids:[1..16 unique UTF-8 sorted], analyzer_ids:[1..16],
  score_ids:[1..16], explanation_ids:[1..16], logical_index_ids:[1..16]
}
```

Every ID is `IdText`; arrays are unique and unsigned-UTF-8 sorted. The client
request contains `required:RequiredContractsV1` and
`limits:{max_frame_bytes:1048576}` only. The result contains protocol,
`provider:"spipe-search-provider/1.0"`, `implementation_digest:HashText`, the
five arrays from `InitializeRequiredIdsV1`, exactly
`ProviderCapabilitiesV1`, exactly `ProviderLimitsV1`, and
`optional_fields:[]`. Protocol 1.0 requires the optional list to be empty;
future minor versions may name at most 32 `IdText` leaf fields, but cannot make
a required/semantic field optional. Unknown nested keys or a value exceeding a
client hard maximum rejects initialization. Negotiated effective limits are
the componentwise minima; they are recorded in generation identity.

## 15. Wave 4 implementation evidence checkpoint (2026-08-25)

Commit `2b9f25f8604` accepts only the Lane C canonical checked-BM25 slice:

- `src/lib/common/search/ranking.spl`;
- `test/01_unit/lib/common/search/ranking_spec.spl`.

Highest-capability review is `PASS`. A clean integration checkout reported the
ranking source check `PASS` and the focused specification `PASS 30/30`. That
execution used bootstrap-seed/non-Stage-4 runtime provenance, so it proves the
accepted scorer slice under that runtime only; it is not Stage 4 runtime
qualification and does not close Wave 4.

The proposed DBFS bundle is `FAIL` and `NOT-EVIDENCE`. Its standalone
`wave4_compatibility` path is a duplicate fixture scorer rather than a facade
over the canonical scorer; probe cells are too weak; asserted clean/parity
evidence was not executed and is false as stated; embeddings zero-use is not
proved; and capability/statistics behavior is defective. No DBFS file from
that bundle is accepted.

The next DBFS slice must be an actual compatibility facade over the canonical
scorer. It must prove idempotent remove/re-add statistics, deduplicated query
terms, advertise `explain:false` until explanation is implemented, and compare
incremental results with an independently rebuilt final corpus. Wave 4 remains
`IN PROGRESS`.

Post-push lint is a separate tooling blocker, not a scorer failure: in the
clean integration checkout,
`bin/simple lint src/lib/common/search/ranking.spl` failed before producing a
lint result because runtime/codegen dispatch could not resolve
`Array.sort_by`. The command also had bootstrap-seed provenance. No duplicate
check was run because the lint owner tool is unresolved and the same seed path
is not qualified.

### 15.1 DBFS facade attempt closure

The clean-clone candidate consisted of exactly:

- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/__init__.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/bm25.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/inverted_index.spl`;
- `src/lib/nogc_sync_mut/db/dbfs_engine/fts/search.spl`;
- `test/02_integration/storage/dbfs/fts_canonical_facade_spec.spl`.

All three permitted execution cycles produced zero owned-code execution. The
Stage 3 Simple runtime,
`9ce412a1d102de421de6d7042d8dc5c65201cc514b463b9b6a5bc5de2f66970c`,
does not provide the required `check` or `test` command. The Rust seed,
`c9c783b8568cf9a199945fe1ee98d08615b728387e6c89cbdc9b50e600f3e091`,
stopped first on unrelated `nogc_async_mut/path.spl` `E1002 unsafe` and
`plan_sdn.spl` `Dedent` failures.

Static highest-capability review is `FAIL` with admissible files `[]`.
`inverted_index` and the engine mutate nested collection/struct fields without
building complete child copies and performing one owner reassignment. The
lexical index commits before trigram/content state, so replacement is not
atomic. The frozen `contains_document` ABI has a `me fn` mismatch. The
focused spec omits intermediate statistics/averages, complete independent
clean-corpus statistics, contains/absent behavior, exact result-order equality,
legacy success, and checked-upsert failure/no-change assertions.

Preserve the canonical-scorer facade direction, checked-operation/capability
intent, and focused regression-fixture shape as design input only. No candidate
file is accepted. The next slice must rebuild and write back value-semantic
child copies, commit the complete engine transaction atomically, correct the
frozen ABI, complete the oracle, and then run a fresh bounded execution on a
capable pure-Simple runtime. Wave 4 remains `IN PROGRESS`.

### 15.2 Canonical analyzer batch/identity contract freeze

The current analyzer candidate is `FAIL`; its admissible file set is `[]`.
Freeze this separate `std.common.search` algorithm seam:

```text
enum SearchFieldIdentityV1:
  Identifier; Title; Heading; Classification; Body

enum AnalyzerErrorV1:
  InvalidLimits; InvalidFieldIdentity; InputLimitExceeded; InvalidUtf8;
  NormalizedLimitExceeded; TokenBytesLimitExceeded; TokenCountLimitExceeded;
  DistinctTermLimitExceeded

struct AnalyzerIdentityV1:
  analyzer_id:text
  unicode_version:text
  unicode_manifest_sha256:text
  normalization_id:text
  lowercase_id:text
  tokenizer_id:text
  stop_words_id:text
  stop_words_sha256:text
  stemming_id:text
  field_schema_id:text
  limits_schema_id:text

struct AnalyzerLimitsV1:
  max_input_bytes:i64
  max_normalized_bytes:i64
  max_token_bytes:i64
  max_tokens:i64
  max_distinct_terms:i64

struct AnalyzedTokenV1:
  value:text
  position:i64
  exact_identifier:bool

struct AnalyzedTextV1:
  normalized:text
  tokens:[AnalyzedTokenV1]

struct AnalyzedQueryTermV1:
  value:text
  qtf:i64

struct AnalyzedQueryV1:
  normalized:text
  terms:[AnalyzedQueryTermV1]

analyze_field_v1(input:text, field:SearchFieldIdentityV1,
                 identity:AnalyzerIdentityV1, limits:AnalyzerLimitsV1)
  -> Result<AnalyzedTextV1,AnalyzerErrorV1>
analyze_query_v1(input:text, identity:AnalyzerIdentityV1,
                 limits:AnalyzerLimitsV1)
  -> Result<AnalyzedQueryV1,AnalyzerErrorV1>
unsigned_utf8_less(left:text, right:text) -> bool
```

This batch seam neither renames nor replaces `ProviderAnalyzerLimitsV1`,
`ProviderAnalyzedTokenV1`, `ProviderAnalyzedTokenSinkPort`, or
`ProviderStreamingAnalyzerV1`. The provider streaming seam adapts the
canonical algorithm layer, and byte-for-byte token/position/error parity is an
acceptance requirement.

V1 analysis is UCD 17.0.0 NFC, Unicode Default Lowercase Conversion (not case
folding), then NFC. Tokens are maximal runs of Unicode `Alphabetic`,
`Decimal_Number`, `Mark`, or `_`. Positions are one-based and assigned
before removing the exact stop-word set `[a,an,and,of,the,to]`, whose SHA-256
is
`6f0a7c26d3d0e3d06a2fbbbeaa1843294f83c3be26baf1c04651191e011510bf`.
For `Identifier`, append the full normalized value last, without trimming,
at position zero, and deduplicate it. Query terms retain QTF and sort by
unsigned UTF-8 bytes.

Query limits are exactly `AnalyzerLimitsV1(4096,4096,4096,128,128)` in field
order. Field input has a hard 1,048,576-byte ceiling; its configured token
count cannot exceed 524,288. The full limit tuple, Unicode manifest digest,
stop-word ID/digest, and field/limit schema IDs participate in snapshot/cache
identity. Analysis performs no embedding, process launch, network access, or
locale-dependent operation.

Analyzer-lane ownership is limited to
`src/lib/common/search/analyzer.spl` and
`test/01_unit/lib/common/search/analyzer_contract_spec.spl`;
`src/lib/common/search/__init__.spl` is merge-owned. The required generated
UCD 17 bundle and manifest from Section 14.7 are absent on `main`, so they are
a prerequisite, not analyzer-lane output. The existing candidate is unbounded
and its parity claim is false; accept none of it. Wave 4 remains
`IN PROGRESS`.

### 15.3 Unicode 17 prerequisite attempt closure

The Unicode prerequisite is one atomic 14-file bundle:

- `examples/05_stdlib/spipe/tools/unicode/generate_unicode_tables.mjs`;
- `examples/05_stdlib/spipe/tools/unicode/UNICODE-LICENSE.txt`;
- the seven files under
  `examples/05_stdlib/spipe/tools/unicode/ucd/17.0.0/`:
  `UnicodeData.txt`, `DerivedCoreProperties.txt`, `PropList.txt`,
  `SpecialCasing.txt`, `CaseFolding.txt`, `CompositionExclusions.txt`,
  and `NormalizationTest.txt`;
- `examples/05_stdlib/spipe/src/search/generated/unicode_17_0_0.js`;
- `src/lib/common/search/generated/unicode_17_0_0.spl`;
- `examples/05_stdlib/spipe/test/fixture/wave4_search/unicode_17_0_0_manifest.json`;
- `examples/05_stdlib/spipe/test/unit/unicode_17_tables_test.js`;
- `test/01_unit/lib/common/search/unicode_17_0_0_spec.spl`.

The attempt repaired its generator toward stable 256-code-point canonical
combining-class buckets with bounded-linear processing, O(n) final-sigma
contexts, and bounded 4,096-element JavaScript output chunks. JavaScript passed
7/7 over all 20,034 normalization vectors in five forms, every scalar, and a
1-MiB case.

This does not admit the bundle. Cycle 2's Simple invocation timed out with exit
124 and no summary on the Rust seed. Cycle 3 merely repeated the already-green
JavaScript check, adding no evidence and violating the bounded process plan.
Highest-capability review is `FAIL` with admissible files `[]`: Simple
push/value-semantics and the optimizer bound remain unproved; the Simple spec
directly calls `rt_file_read_text` instead of the required facade; requirement
`REQ-SPK-SEARCH-UNICODE-001` is orphaned; the generated JavaScript license
path is wrong; and the independent lowercase matrix is weak for
`Case_Ignorable` final-sigma contexts.

Accept no file from the bundle. The analyzer's Unicode prerequisite therefore
remains absent. The next session must repair every static defect first, then
run the complete Simple parity suite exactly once on a capable pure-Simple
runtime. Wave 4 remains `IN PROGRESS`.
