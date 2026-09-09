# SPipe local knowledge setup

SPipe keeps reusable common knowledge separate from company, organization,
project, user, and host knowledge. The project records the common revision;
machine-specific checkout paths remain in a private local registry.

## Existing first-user setup compatibility

From a SPipe checkout on Unix:

```sh
sh scripts/setup-local-knowledge.sh --mode user
```

The default creates a user-owned repository at `~/.spipe`, mounts common SPipe
as `~/.spipe/.spipe`, creates `organization/` and `projects/`, and ignores
`local/`. It does not create a remote or upload content. PowerShell users run
`scripts/setup-local-knowledge.ps1 -Mode user`.

The September 9 target layout uses common at `~/spipe`, a private workspace at
`~/.spipe`, and `~/.spipe/common -> ~/spipe`. Simple's common route should point
through `.spipe/common` to the canonical checkout after reviewed integration. The earlier nested
installation remains a migration fallback. The supplied Node install/workspace
scripts are reference-package proposals; their integration is not established
by this guide. Continue using the available host bootstrap until that cutover.

## After cloning a project

Run the host bootstrap:

```sh
sh scripts/setup-spipe-local.shs --project <logical-project-id>
```

On PowerShell, run `scripts/setup-spipe-local.ps1 -Project <id>`. The bootstrap
initializes the revision already recorded by the project. Current legacy hosts
with `.spipe/spipe` are supported without moving or overwriting their state.

## Ownership and updates

- Common: generally reusable procedures and public knowledge.
- Company: company-owned policy and infrastructure knowledge.
- Organization: organization-owned rules and decisions inside or across a company.
- Project: architecture, requirements, tests, incidents, and project evidence.
- User: authored personal knowledge; preferences remain local configuration.
- Host: machine-specific authored knowledge that is safe to retain canonically.
- Local registry: absolute paths and personal machine configuration.

Research composes authorized `wiki/` scopes in this order:

```text
common -> company -> organization(s) -> project(s) -> user -> host
```

Each knowledge-owning scope uses `raw/` for evidence, `wiki/` for synthesized
knowledge, `doc/` for normative lifecycle artifacts, and `skills/` for agent
procedures. Create surfaces lazily and put `index.md` in each present traversable
directory. `runtime/<user>/<host>/cache/` is reconstructible;
`state/` retains research history and resumable runs; `run/` holds active
coordination; `tmp/` holds bounded temporary material. Cache cleanup must retain
state and active run files. Runtime never grants canonical authority.

Start at a scope's `index.md`. Update the smallest owner-controlled canonical
lifecycle document, validate its evidence and links, and refresh only dependent
indexes or summaries. Rebalancing produces a proposal by default. Publishing
organization/project material into common requires owner approval and a
sanitized independent artifact.

The canonical reusable instructions live in the SPipe common submodule under
`doc/00_llm_process/knowledge/` and the `knowledge-ownership` skill.

## Workspace and research integration target

Company content belongs under `companies/<company>/`; departments use its
`organizations/<organization>/`. `projects/<id>/` registers independent project
repositories. Personal knowledge belongs to `users/<user>/`, shared machine
knowledge to `hosts/machines/<host>/`, and private account paths to
`users/<user>/hosts/<host>/mounts.json`. Host defaults/profiles describe desired
setup; runtime probes provide actual capability evidence.

The canonical resolver selects explicit `SPIPE_HOME`, project `.spipe/common`,
`~/spipe`, `~/.spipe/common`, direct current SPipe package, then verified
legacy mounts. This latest order supersedes the supplied package's
project-local-first preference. Existing pins still require validation; route
migration never silently upgrades or removes a recorded submodule.

Load task skills, enter authorized scope/wiki indexes, retrieve relevant leaves,
reuse only matching runtime state, then follow `doc` for approved decisions and
`raw` for exact evidence. Research remaining external gaps, verify provenance,
and propose owner-correct writeback. Scope registration does not grant access
to sibling departments. Keep `doc/00_llm_process/knowledge/` as documentation
about the system when adding top-level wiki knowledge.

Classify legacy `local/` entries individually. Preserve unknown files pending
owner review; separate retained history from cache and convert registries by
schema. The reference inventory is read-only and is not a migration executor.
Internet install, intranet-mirror consumption, and legacy pinned-project use
are supported design paths; mirror publication is a separate explicit workflow.
