# Local research: bug-linked workarounds

Research date: 2026-09-30. Scope: host Simple bug tools and bootstrap workflow.

Existing `src/app/check_dbs/main.spl` loads the canonical bug database through
`std.database.bug`; the concrete implementation is
`src/lib/nogc_sync_mut/database/bug.spl`. Extend this lookup with a derived text
index rather than a second authority for bug status. New annotation/index
ownership belongs in `src/app/bug/`.

`doc/07_guide/tooling/bootstrap_cache_policy.md` already defines exact producer
and entry bindings, scoped phase invalidation, retained failed attempts, and
deferred clean qualification. Workaround tracking must preserve these rules.
The wrapper currently invalidates at phase-entry scope; dependency-only rebuild
is available only when the owning cache proves that narrower scope correct.

Agent entrypoints are `.claude/rules/bootstrap.md`,
`.codex/skills/unstable-build-fixes/SKILL.md`, and
`.claude/skills/lib/debug.md`. Host SPipe term routing belongs in
`doc/00_llm_process/llm_wiki.md` and `llm_wiki_and_auto_research.md`.
The SPipe core is separately owned; host wiki links avoid modifying a pinned
submodule or the stale vendored SPipe copy.

I/O route observed in this checkout: `app.io` exports `app.io.mod`, which imports
`std.nogc_sync_mut.io.file_ops`, `process_ops`, and `env_ops`.
These owners contain runtime bridges; this research does not establish that
all current bridges already traverse SOSIX. New app code uses these facades.
Any new runtime host operation must follow the existing SOSIX boundary and be
audited explicitly instead of declaring local `rt_*` externs in app leaves.

Primary risk: making a cheap bug check recursively inspect the repository.
The chosen split makes discovery a build/maintenance operation and lookup an
index-plus-bug-database operation. Missing index and changed HEAD report stale
state without hidden discovery.
