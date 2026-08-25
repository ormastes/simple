# SPipe Knowledge Compiler Feature Expert

Use this entry when work concerns stable documentation identity, knowledge
parsing, workspace registries, trace graphs, search, virtual documentation
views, safe refactors, tree organization, or common-knowledge promotion.

Canonical operator guide:
`doc/07_guide/app/spipe/spipe_knowledge_compiler.md`.

Current reachable implementation is Wave 2 in
`examples/05_stdlib/spipe/src/{model,parser,workspace,storage,core}` with schemas
under `examples/05_stdlib/spipe/schema`. It supports bounded explicit-input
inventory compilation, immutable records/snapshots, provisional identity,
opaque durable UID proposals, identity diagnostics, and isolated worktree
overlays. Do not claim planned index/search/view/trace/refactor CLI commands are
reachable before their dependency waves land.

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

Related experts:

- `doc/00_llm_process/layer_expert/infra_storage/skill.md`
- `doc/00_llm_process/feature_expert/cache_identity/skill.md`
- `doc/00_llm_process/feature_expert/mcp_runtime/skill.md`
