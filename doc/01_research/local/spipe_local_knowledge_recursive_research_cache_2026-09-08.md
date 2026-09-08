<!-- codex-research -->
# SPipe + Slang: local knowledge ownership, recursive research, and cache-aware execution

Date: 2026-09-08. Status: user-supplied final research, condensed for the
repository. The complete report was supplied in the originating Codex session;
this artifact preserves its decisions, evidence map, implementation sequence,
and cautions without claiming new benchmarks.

## Decisions

- Use independently owned `common`, `organization`, and `project` scopes.
  Common is the shareable SPipe distribution. Organization and project roots
  remain user-controlled local checkouts; registration never copies or grants
  access. Personal preferences are local configuration.
- Keep one canonical writable artifact per UID, lifecycle-first project docs,
  typed forward references, derived reverse references, and generated views.
  Every traversable wiki node has `index.md`.
- Separate canonical storage, navigation views, and prompt/cache packs.
- SPipe owns retrieval, provenance, traversal, prompt construction, provider
  adapters, and cache planning. Slang owns model execution state, exact token
  prefixes, KV blocks, isolation, eviction, and optional transport. Hosted-only
  SPipe must work without Slang.
- Start with structural chunks, sparse references, and the existing
  `deterministic_components_greedy_bounded_v1`. Gate Leiden and hypergraph
  refinement behind held-out evidence and stability checks.
- Learn from validated cross-document use, not mere prompt insertion. Reorder
  only for strictly greater than 10% effective-use improvement plus independent
  observation, persistence, and amortization guards.
- Exact prefix reuse is the baseline. Links, summaries, prompt manifests, and
  KV tensors are distinct objects. Non-prefix KV fusion remains experimental.

## Repository corrections

At the inspected snapshots, standalone SPipe already had a research-agent
surface. Simple's embedded SPipe contained `analyzeRebalanceV1` with bounded
deterministic grouping and explicit omissions including Leiden, multilevel
partitioning, local refinement, and physical moves. The released CLI spec did
not expose rebalance/promotion commands. Slang had resident request generation,
but explicitly lacked continuous batching, chunked prefill, and prefix caching;
the ggml shim used global context/model handles and cleared context before each
prefill. That clear is the safe baseline, not a cache implementation. Product
readiness documentation lagged the engine source.

## Ownership and composition

The logical workspace selects pinned common content, an optional authorized
organization, and one or more projects. Registries record logical identities,
roots, revisions, policies, and dependencies. Absolute paths, credentials, and
private details remain local. Evidence composes with provenance; it is not
last-file-wins. Organization restrictions cannot be weakened by a project skill.

General public methods belong in common, company policy in organization scope,
project architecture/tests/incidents in project scope, and machine choices in
local configuration. Promotion is separate from rebalancing: create a sanitized
artifact with a new identity after rights/confidentiality review and owner
approval, retaining private provenance only in its original scope.

## Knowledge, grouping, and execution

Indexes contain stable must-know facts, routes, evidence groups, and exceptions;
volatile counts/ranks/frontier state live outside the stable prefix. Raw sources
are immutable revisions with original/extracted hashes, extraction version,
source identity, section IDs, dates, and rights metadata. Derived summaries bind
exact source revisions and generation/validation identity.

Build sparse authorized evidence graphs from explicit links, supported task
co-use, lexical/structural affinity, optional versioned embeddings, and weak
co-change signals. Preserve exact/lexical escape search, manual boundaries,
stable section/group UIDs, and held-out quality evaluation. Runtime packs use a
bounded prefix trie per security domain, task family, and provider profile.

The prompt compiler emits an immutable logical manifest, then a versioned
provider rendering: stable role/tools; common, organization, project and ancestor
cores; stable summaries/manifests; ordered raw evidence; reusable-prefix
boundary; then the original question and volatile routing/output requirements.
Tokenize the complete rendered sequence, not independent fragments.

SPipe owns durable depth-first traversal with post-order summaries. Routers may
select only authorized UIDs. Results carry claims, exact evidence revisions,
coverage states, applicability, contradictions, and gaps. Enforce depth/node/
token/cost/time/retry bounds, cycle detection, immutable snapshots, bounded
repair, exact/BM25 fallback, resumable state, and publication-time freshness.

## Provider and cache contracts

Claude Code, Codex, direct APIs, Slang, and generic hosted adapters share probe,
render, run, resume, cancel, and normalized usage contracts. Capabilities are
versioned and honestly reported; unknown profiles fall back restrictively.
Provider-export policy is enforced before local CLI or API launch.

Distinguish source store, summary/result cache, prompt manifest, and KV cache.
Coverage is `raw_embedded`, `prefix_attached`, `summary_only`, `manifest_only`,
or `unavailable`; cache observation is separately eligible/hit/miss/unknown.
Hosted caches require provider-documented exact-prefix controls and cannot be
exported as local tensors.

Slang proceeds through instrumentation/capabilities; serial backend-owned exact
prefix snapshot/restore; immutable paged KV with copy-on-write; CPU/SSD tiering;
authenticated distributed lookup/transfer; and only then optional non-prefix
fusion research. Cache identity includes security domain, policy, model,
tokenizer, adapter, positional/attention configuration, dtype/layout, sharding,
and backend ABI. Transfer occurs only when lookup, transfer, restore, and queue
cost beat recomputation.

## Implementation sequence and acceptance

W0 reconciles standalone/embedded ownership and baselines. W1 adds scope
registry, mounts, policy, immutable source IDs, indexes, and readiness metrics.
W2 adds hosted DFS/manifests/results and CLI adapters. W3 adds direct API cache
adapters and serial exact-prefix validation. W4 adds event data, stable bundle
ordering, 10% hysteresis, and paged KV. W5 adds virtual rebalance, reviewed wiki
updates/contribution, and tiered storage. W6 adds optional advanced grouping and
distributed KV. Hosted support must not wait for local cache work.

Acceptance covers cross-scope isolation, personal projects, ambiguous names,
missing mounts, link-only evidence, changed-prefix invalidation, unchanged-file
stability, authorization revocation, provider cache uncertainty, DFS bounds,
prompt injection resistance, promotion secret checks, Slang concurrency and
eviction safety, ABI rejection, corruption fallback, incremental/full rebuild
equivalence, deterministic rendering, and cached/uncached numerical parity.

## Evidence register

Repository evidence: standalone SPipe research agent; embedded rebalance
analysis; rebalance/promotion system specification; Slang engine; ggml shim; and
Slang README at the revisions named in the supplied report. Prior local designs:
`spipe_knowledge_compiler_virtual_views_design_plan_2026-08-25.md` and
`spipe_document_knowledge_refactoring_design_and_plan(1).md`.

External primary sources: Traag et al. on Leiden (arXiv:1810.08473); dynamic
Leiden (arXiv:2405.11658); RAPTOR (arXiv:2401.18059); KaHyPar; NAACL 2025
semantic-chunking findings; official OpenAI prompt-caching, Codex subagent, and
noninteractive docs; official Anthropic caching, subagent, headless, and Claude
Code caching docs; vLLM prefix caching; CacheBlend (arXiv:2405.16444); SGLang
HiCache; and LMCache architecture. Provider details are version-sensitive and
must be re-probed at implementation time.
