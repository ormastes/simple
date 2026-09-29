<!-- codex-architecture -->
# SPipe Knowledge Compiler Architecture — TLDR

SPipe keeps one lifecycle-first canonical tree and compiles it into an immutable
typed `KnowledgeSnapshot`. Artifact/section UIDs are identity; paths, headings,
keys, aliases, and every feature/component/layer/trace tree are names or
read-only projections.

## Core shape

`KnowledgeCompiler` is the sole parent publication authority. Parsers,
identity, graph, index, projections, and diagnostics return deterministic
deltas. `RefactorService` alone writes canonical files. Rebalancing and common
promotion return proposals only. Security, metrics, cache policy, and tracing
wrap stable ports as MDSOC feature transforms; Simple/JS implementations are
runtime adapters.

## Resolved contracts

- Edges store one active-verb direction: evidence/test/source/task -> what it
  supports, verifies, implements, or schedules. Inverses are query views.
- Explicit and deterministic generated accepted edges may satisfy strict trace;
  structural, lexical, semantic, and LLM inference remain proposals.
- Stable section markers are mandatory once a section is referenced, traced,
  or transaction-managed. Heading rename retains UID and slug alias.
- Shared state is limited to immutable committed content-addressed segments.
  Dirty overlays, locks, journals, materialized views, and private caches are
  isolated by repository + worktree identity.
- Transactions durably journal plan, original/intended hashes and staged bytes
  before mutation; atomic apply is validated before snapshot publication.
  Startup resumes or rolls back from hashes and never guesses.
- `AuthorizationPort` alone issues transaction/snapshot/path-bound
  `SafeFilesystem.Refactor` to `RefactorService` and
  `SafeFilesystem.Materializer` to the authorized `ProjectionService`
  materializer adapter; filesystem ports neither issue nor route capabilities.
  `RefactorService` holds its capability locally while invoking
  `RefactorSafeFilesystemPort`. The projection adapter derives a sanitized,
  non-authorizing `MaterializerRootGrant`; only that grant crosses
  `MaterializerSafeFilesystemPort`. Providers never receive either capability.
  The capabilities are non-implying; both APIs are descriptor-relative/no-follow.
- Rebalancing must-links cover generated spec/manual pairs and explicitly
  protected bundles. Trace is normally weighted, avoiding giant collapsed
  clusters; strict policy can co-locate sole verification evidence explicitly.
- MCP negotiates an explicit supported version, preserves legacy stdio, targets
  `2026-07-28`, exposes deterministic pagination, and never marks private or
  authorization-filtered content publicly cacheable.
- URI/MCP views are blocked on Wave 5a `SnapshotAuthorityPortV1`: only its
  opaque workspace/project/worktree/snapshot/revision-bound view can prove
  manifest target-kind/UID membership before `ProjectionPortV1` renders. Raw
  snapshot-store lookups, asserted targets, and duck-typed port substitutes
  fail closed.
- Target membership is anchored by a sealed, content-addressed inventory root.
  Resolver order proves workspace/worktree + snapshot + canonical target before
  receipt verification; workspace aggregates are explicit null-project manifests
  and worktree binding is transitive through the verified manifest tuple.
- The seal is two-level and non-cyclic: `TargetInventoryManifestV1` binds a
  base snapshot UID, then `AuthorityManifestV1` binds that base UID plus the
  inventory root. The sealed alias index is resolved through SnapshotAuthority,
  never by an external path lookup.
- Dependency-free JS is the normative lexical provider. Simple acceleration
  must match tokenization, fixed-point scores, ties, explanations, updates, and
  exhaustive top-k exactly; optional semantics only add candidates.
- Provider cooperative streaming is specified in
  `spipe_knowledge_compiler_cooperative_streaming.md`: one session owner keeps
  bytes raw through bounded framing/iterative JSON, steps SHA/Unicode/work
  machines, arbitrates cancel/deadline before commit I/O, and advertises
  `cancel:true` only after a real framed-cancel qualification test.

## Runtime and security

Startup recovers journals and loads manifests/aliases lazily—no full scan.
List/read/resolve/search/trace pin one snapshot and perform no writes, retry
sleeps, repeated rereads, or per-request subprocess launches. Deltas invalidate
only affected objects, reverse edges, postings, projections, and diagnostics.

All URIs resolve through registered workspace/project/revision/UID. Realpath
and deny-wins authorization reject traversal, symlink/junction escape,
cross-root mutation, cache leakage, and unapproved view writes. Repository text
is untrusted data, not agent policy. Remote semantics is explicit opt-in.

## Wave-0 qualification candidates

- Absolute latency values are candidates until Wave 0 locks the hardware,
  corpus, provider, and measurement profile; they are not unconditional gates.
- Warm startup candidate <=250 ms P95; exact resolve/read <=20 ms.
- Warm list candidate <=50 ms and lexical search at 50k artifacts <=100 ms P95.
- NFR-SPKC-014 remains normative: median warm one-artifact update is at least
  20x faster than full rebuild on the qualified fixture.
- Unchanged virtual files rewritten: zero; required provider parity: 100%.

Inspect the full architecture at
`doc/04_architecture/infra/spipe/spipe_knowledge_compiler.md`.
