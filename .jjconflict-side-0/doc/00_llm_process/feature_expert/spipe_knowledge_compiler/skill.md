# SPipe Knowledge Compiler Feature Expert

Use this entry when work concerns stable documentation identity, knowledge
parsing, workspace registries, trace graphs, search, virtual documentation
views, safe refactors, tree organization, or common-knowledge promotion.

Canonical operator guide:
`doc/07_guide/app/spipe/spipe_knowledge_compiler.md`.

## CURRENT STATE (measured 2026-09-05 — read this first)

**The implementation is pure Simple at `src/app/spipe/`, not the JavaScript
package.** Everything below the "Wave 2--3 (JS-era)" heading describes
`examples/05_stdlib/spipe`, which is frozen legacy; it is retained for its
invariants, which still hold, but it is NOT a description of the live tree.

There are **six disjoint SPipe locations**. Know which one you are touching:

| Location | Lines | State |
|---|---:|---|
| `src/app/spipe/` — knowledge compiler | 3,952 | 11 units, **2 CLI verbs**, 7 unreachable, 0 CI gates |
| `src/app/spipe_mcp/main.spl` | 543 | ~33 tools, **runnable but NOT in `.mcp.json`** |
| `src/lib/nogc_sync_mut/spipe/` | 1,094 | what that server serves — also undeployed |
| `src/app/spipe_knowledge_provider/` | 9,429 | out-of-process lexical provider; `search/process_adapter.spl` already speaks to it |
| `examples/05_stdlib/spipe/` (JS) | 8,649 | frozen legacy |
| `.spipe/spipe` (JS v0.1.0) | — | separate repo, deferred debt |

Load-bearing facts an implementing agent must not rediscover:

- `src/app/spipe/main.spl:114-139` dispatches only `registry`, `admit`, `--help`,
  `-h`. Seven units are unreachable from any operator surface: balance, refactor,
  scan, fusion, graph, identity, search. (`model` is reached only for two type
  definitions at `main.spl:20`.)
- `main.spl:3-4` claims `scan`/`balance` "do not exist yet". **They do** — that
  comment is stale.
- `src/app/spipe_mcp` imports `app.spipe.*` **zero times**, and is itself absent
  from `.mcp.json` — the deployed servers are `simple-mcp`,
  `simple-lsp-mcp` and `stitch`. The surface agents actually reach is `simple_ctx_*`.
- Nothing under `src/app/spipe/` is referenced by `config/check/must_check_gates.sdn`
  or any `scripts/check/*.shs` gate.
- **Three BM25 implementations exist.** `common/search`'s `struct InvertedIndex`
  (`inverted_index.spl:68`) has **zero product consumers**; `index_engine_provider.spl`
  and `simple_ctx_*` each scan per query; `dbfs_engine/fts`'s `FtsInvertedIndex`
  is the only wired index (via `app/io/context_ops.spl:475`). Do not add a fourth.
- `refactor/plan.spl` IS covered — by `refactor_rewrite_spec.spl:26,96`, not by a
  file of its own. Do not write a duplicate spec.
- `src/app/llm_process_gen/` already compiles these `skill.md` files — do not
  write a second skill compiler.

Plan of record: `doc/03_plan/infra/spipe/spipe_knowledge_compiler_refined_plan.md`
(Revision 3 — §1.5 measured ground truth, §4.1a re-decided waves, §9 Slice 2).
Architecture: `doc/05_design/infra/spipe/spipe_knowledge_base_architecture.md`.
Research: `doc/01_research/infra/spipe/llm_knowledge_tooling_landscape_2026-09-05.md`.

## Wave 2--3 (JS-era, SUPERSEDED — invariants below still bind)

Waves 2--3 provide bounded explicit-input
inventory compilation, immutable records/snapshots, provisional identity,
opaque durable UID proposals, identity/graph diagnostics, and isolated
worktree overlays in
`examples/05_stdlib/spipe/src/{model,parser,workspace,storage,core,graph}` with
schemas under `examples/05_stdlib/spipe/schema`.

Two later narrow slices are admitted in commit `6b7fc8b83f6`:

- `ProjectionKernelV1` canonically parses `spipe://` targets and performs
  deterministic list/read over a caller-authorized immutable inventory.  Its
  unsigned base64url cursor is an unauthenticated local continuation: it
  equality-checks its bound fields, but integrity/signing and authorization
  remain a deferred adapter responsibility.  The kernel does not open
  snapshots, authorize a reader, route MCP, materialize files, or write
  canonical content.
- `SnapshotLexicalSearchV1` performs fixed-point lexical discovery over sealed
  identifier, title, and classification metadata.  Its root binds workspace,
  snapshot, authorization-scope digest, and metadata-index root.  It is not
  body/full-text search, a provider bridge, persistence, or incremental
  indexing.

The selected transactional `AuthorityServiceV1` is presently a
trust/composition and wire-contract prerequisite, not an admitted authority
backend.  It is the future sole mutable owner of publish, resolve, and canonical
open; Node clients fail closed and have no filesystem, pointer, lock, CAS, or
fallback authority.  Optional F2/N2 native storage is private to a certified
service composition root.  Do not claim availability, durability,
linearizability, RPO/RTO, service IPC success, MCP exposure, virtual-view
materialization, full-text/provider search, persistence, or canonical mutation.

The supplied trace-kernel candidate is frozen and **unadmitted** after its
review cap because duplicate-reference validation remains defective.  It is
forensic material only and must not be copied into implementation prompts or
used as traceability evidence.  Do not claim planned index/search/view/trace/
refactor CLI commands are reachable before their dependency waves land.

Rules:

- Paths, titles, semantic keys, and content hashes never become durable UIDs.
- Provisional `P-<project>-<content-hash>` identity is snapshot-scoped and is
  invalid for strict trace, mutation, durable aliases, or cross-revision use.
- Keep semantic project dependency separate from physical linkage.
- Dirty state changes only the worktree overlay hash; `revision_id` remains the
  resolved committed/base revision.
- Reuse the single canonical SnapshotId implementation and exact `spks1-` tuple.
- Never share dirty overlays, locks, journals, or mutable current state across
  worktrees.
- Core compilation consumes an explicit bounded input set; containment-safe
  enumeration belongs to the workspace adapter.
- Treat a `ProjectionKernelV1` rendering as caller-scoped immutable projection
  output and `SnapshotLexicalSearchV1` results as lexical candidate hits;
  neither is an authorization receipt or canonical ownership.
- For any future publish/open request, preserve the P2 replay envelope and use
  the service request/resolve protocol; a local file operation, raw URI, cache,
  or unverified response cannot establish authority.
- Keep rejected/frozen candidates marked non-admitted in plans, guides, and
  agent state.  Passing narrow tests never upgrades them to a released surface.

Related experts:

- `doc/00_llm_process/layer_expert/infra_storage/skill.md`
- `doc/00_llm_process/feature_expert/cache_identity/skill.md`
- `doc/00_llm_process/feature_expert/mcp_runtime/skill.md`
