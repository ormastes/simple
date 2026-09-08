# SPipe local knowledge setup

SPipe keeps reusable common knowledge separate from organization and project
content. The project records the common revision; machine-specific checkout
paths remain in a private local registry.

## First user setup

From a SPipe checkout on Unix:

```sh
sh scripts/setup-local-knowledge.sh --mode user
```

The default creates a user-owned repository at `~/.spipe`, mounts common SPipe
as `~/.spipe/.spipe`, creates `organization/` and `projects/`, and ignores
`local/`. It does not create a remote or upload content. PowerShell users run
`scripts/setup-local-knowledge.ps1 -Mode user`.

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
- Organization: company policy, private infrastructure, and organization-wide
  decisions.
- Project: architecture, requirements, tests, incidents, and project evidence.
- Local registry: absolute paths and personal machine configuration.

Start at a scope's `index.md`. Update the smallest owner-controlled canonical
lifecycle document, validate its evidence and links, and refresh only dependent
indexes or summaries. Rebalancing produces a proposal by default. Publishing
organization/project material into common requires owner approval and a
sanitized independent artifact.

The canonical reusable instructions live in the SPipe common submodule under
`doc/00_llm_process/knowledge/` and the `knowledge-ownership` skill.
