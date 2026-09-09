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
knowledge-owning scope exposes `index.md`; content surfaces are created lazily
and each existing traversable surface has its own `index.md`.

`runtime/<user>/<host>/` is never canonical knowledge. Its `cache/` is
reconstructible, `state/` retains resumable runs/history/receipts, `run/` holds
live coordination, and `tmp/` has a bounded lifetime. Cache cleanup must preserve
retained state and live coordination. Reuse
requires matching authorization, source revisions, task applicability,
schema/provider profile, and expiry. Rebuilding cache preserves authoritative
results; deleting the whole runtime tree can destroy retained work.

## Planned shared boundary

Provider prompts and plugins should consume shared contracts rather than
duplicate resolution logic: `locate_common()`, `resolve_workspace()`,
`resolve_active_scopes()`, `compile_research_context()`, and
`explain_resolution()`. These names are proposed until implemented and tested.

Preserve `.spipe/.spipe`, project `.spipe` pins, and legacy `.spipe/spipe`
discovery. Keep `doc/00_llm_process/knowledge/` as documentation about the
knowledge system; it is not renamed to `wiki/`.

## September 9 workspace-package refinement

The fuller user-supplied package supersedes the earlier default physical layout:
new global common is `~/spipe`, the private workspace is `~/.spipe`, and
`~/.spipe/common` links to the common checkout. Existing nested/direct submodules
remain compatibility installations with their exact pins preserved.

Private ownership roots are `companies/<company>/`, its
`organizations/<organization>/`, `projects/<project>/` registrations,
`users/<user>/`, and `hosts/machines/<host>/`. Shared desired host defaults and
profiles live under `hosts/defaults.json` and `hosts/profiles/`; account-specific
mounts live in `users/<user>/hosts/<host>/mounts.json`. Projects retain their
canonical documents in their independently owned repositories. Company identity
does not confer access to sibling departments.

The latest user refinement selects canonical `~/spipe` and a Simple project
common route `.spipe/common` to that checkout. It supersedes the package's
project-local-first order: resolve explicit `SPIPE_HOME`, project `.spipe/common`,
`~/spipe`, `~/.spipe/common`, the direct current SPipe package, then verified
legacy `.spipe/spipe`, `.spipe/spipe_project`, direct `.spipe` gitlink, or
`~/.spipe` package. Explicit invalid selections fail with a diagnostic. Existing
project pins remain requirements until a separately reviewed migration updates
them; a global mismatch is diagnosed rather than silently accepted. Resolve
common and workspace identities independently. This documentation does not
move or delete the existing submodule.

The supplied Node bootstrap, mirror/install scripts, schema-2 JSON, and claimed
25-test TAP result describe a separate reference package. They are neither
upstream availability nor execution evidence for this repository. Internet,
intranet mirror, and pinned-project acquisition are separate deployment modes;
mirror publication has separate authority from ordinary installation. The
upstream integration plan must retain one shared resolver and registry writer,
typed preference conflicts, trusted policy checks, and reviewed migration.
