<!-- codex-research; Astra-reviewed -->
# SPipe scope-aware LLM wiki research addendum

Date: 2026-09-09. Status: user-supplied research contract, reconciled with the
September 8 local-knowledge design. This addendum preserves the new decisions;
it does not claim that the proposed shared resolver APIs or runtime reuse are
already implemented.

## Selected semantic model

Research context is composed deterministically as:

```text
common/wiki -> company/wiki -> organization(s)/wiki -> project(s)/wiki
            -> user/wiki -> host/wiki
```

Optional scopes are skipped. Multiple organizations and projects follow the
workspace's explicit order, with stable scope identity as a tie-breaker. This
order controls prompt composition, not authorization or last-writer-wins truth:
restrictions accumulate and contradictions retain provenance and applicability.

The content kinds are:

```text
raw/     evidence and source captures
wiki/    synthesized LLM knowledge
doc/     normative lifecycle artifacts
skills/  agent procedures
runtime/ derived execution/research state and cache
```

Company and organization are distinct owners. Authored user and host knowledge
can be canonical; personal preferences remain local configuration. Every
knowledge-owning scope exposes `index.md` plus `raw/index.md`, `wiki/index.md`,
`doc/index.md`, and `skills/index.md`.

`runtime/<user>/<host>/` is disposable and never canonical knowledge. Reuse
requires matching authorization, source revisions, task applicability,
schema/provider profile, and expiry. Deleting runtime must preserve correctness.

## Planned shared boundary

Provider prompts and plugins should consume shared contracts rather than
duplicate resolution logic: `locate_common()`, `resolve_workspace()`,
`resolve_active_scopes()`, `compile_research_context()`, and
`explain_resolution()`. These names are proposed until implemented and tested.

Preserve `.spipe/.spipe`, project `.spipe` pins, and legacy `.spipe/spipe`
discovery. Keep `doc/00_llm_process/knowledge/` as documentation about the
knowledge system; it is not renamed to `wiki/`.
