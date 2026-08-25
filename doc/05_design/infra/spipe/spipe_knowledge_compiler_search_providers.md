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
remain outside that package. SPipe talks to either its dependency-free
JavaScript implementation or a Simple provider through one versioned protocol;
it never imports Simple implementation details.

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
  -> SearchProviderPort
       -> JsSearchProvider (in-process fallback)
       -> SimpleProviderClient (bounded child-process protocol)
              -> SpipeKnowledgeProvider app
                   -> CommonLexicalSearch
                   -> DuplicateCandidateService
                   -> SourceSymbolService

CommonLexicalSearch
  <- DBFS adapter
  <- PureDatabase adapter
  <- TextualDatabase BM25 side-index
  <- DatabaseServer SearchCapsule
```

Parent-owned orchestration rules:

- SPipe owns provider selection, health, retry policy, and query deadlines.
- Each database owns transaction and snapshot boundaries for its index.
- `SpipeKnowledgeProvider` owns request validation and bounded serialization.
- Common search code is pure algorithm/data code and performs no file, process,
  environment, network, or authorization operations.
- Duplicate and symbol services return immutable results; they do not edit
  source or documentation.

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

### 3.6 Index semantics

`LexicalIndexPort` supports:

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
`src/app/spipe_knowledge_provider/main.spl`. SPipe starts at most one provider
per workspace process and communicates over stdin/stdout framed messages. It
must not spawn one process per request.

Each frame is:

```text
8 hexadecimal bytes payload length
payload bytes encoded as canonical JSON
```

The length is counted in bytes, not characters. The reader rejects malformed
hex, frames above the negotiated maximum, invalid UTF-8, duplicate critical
keys, trailing data, and unknown required protocol versions. Stderr is bounded
diagnostic output and never part of the protocol.

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
{"id":"1","op":"initialize","protocol":1,"client":"spipe","limits":{"max_frame_bytes":1048576}}
```

Provider response includes:

```text
protocol = 1
provider name/version/build identity
score contract = bm25-fixed-v1
analyzer identities
capabilities: index_delta, lexical, phrase, explain, duplicate, symbols,
              optional semantic, optional ann
limits: frame bytes, documents per delta, query bytes, result count,
        explanation terms, deadline range
```

No request except `initialize` is accepted before a successful handshake.
Capabilities are descriptive and immutable for the process lifetime.

### 4.3 Request envelope

Every request contains:

```text
id                 opaque client correlation ID
op                 closed operation vocabulary
workspace          stable workspace UID
snapshot           required snapshot or expected parent snapshot
deadline_ms        relative bounded deadline
payload            operation-specific object
```

Responses contain the same ID, `ok`, and exactly one of `result` or `error`.
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

The client treats every provider response as untrusted input even after binary
verification. It requires exactly one outstanding request with the returned
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
| Client deadline | 50 ms minimum, 30 s maximum |

The parser accounts for expansions before execution and rejects over-budget
queries rather than truncating them into different semantics. Search also has
provider-configured postings visited, candidates scored, CPU, allocation, and
output budgets; exceeding any budget returns `limit_exceeded` or
`deadline_exceeded` with no partial page unless the operation explicitly
negotiated typed partial results. Regex queries and leading unbounded wildcards
are not supported in protocol v1. Duplicate and semantic operations use bounded
candidate buckets and cannot request an all-pairs scan through this hot path.

### 4.5 JavaScript parity

The dependency-free JavaScript fallback implements the same logical records,
analyzer identity, `bm25-fixed-v1`, ordering, pagination, error codes, and
explanations. It is in-process and therefore does not implement framing, but a
protocol adapter runs the shared conformance vectors against it.

Optional capabilities may differ. SPipe chooses features from the handshake;
it never changes lexical semantics based on provider availability. A Simple
provider crash degrades to the JS provider only after reopening/rebuilding the
same logical snapshot and records a diagnostic. Results from two different
score/analyzer contracts must never share a cache entry.

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
- dense-vector comparison behind `SemanticProvider`.

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

Stable errors include:

```text
unsupported_protocol, incompatible_contract, invalid_request, frame_too_large,
deadline_exceeded, cancelled, snapshot_not_found, snapshot_conflict,
analyzer_mismatch, unauthorized, limit_exceeded, provider_unavailable,
index_corrupt, semantic_unavailable, internal
```

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
- JavaScript fallback;
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
| Safe fallback | Simple provider crash resumes through JS with an explicit degradation diagnostic |
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
   smoke and JS fallback parity.
8. **Database server:** capability/snapshot/durability contract, exhaustive
   implementation. Gate: leakage, recovery, bounds, and concurrency tests.
9. **Optimizations:** segments, WAND, Block-Max WAND, optional ANN/semantic and
   sharding, one at a time. Gate: exact exhaustive parity plus measured benefit.

No later wave repairs an earlier contract silently. A required contract change
increments its version, regenerates the golden corpus explicitly, documents the
migration, and prevents mixed-version cache reuse.

## 13. Completion checklist

- One documented `bm25-fixed-v1` implementation contract governs all adapters.
- Exact lengths and deterministic public-ID tie-breaking are used everywhere.
- JS fallback and Simple provider pass the same conformance corpus.
- Provider startup, hot request, cache, invalidation, bounds, and fallback paths
  have executable evidence.
- PureDatabase cache identity includes columns, algorithm, and generation.
- DB server search is field-authorized and snapshot-consistent before release.
- Duplicate primitives no longer require compiler ownership, while the legacy
  CLI remains compatible.
- Simple symbol export is compiler-authoritative and revisioned.
- Every optimized path matches the exhaustive oracle.
- Performance and security gates pass without embeddings or a remote service.
