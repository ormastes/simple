# SPipe local knowledge setup

SPipe keeps reusable common knowledge separate from company, organization,
project, user, and host knowledge. The project records the common revision;
machine-specific checkout paths remain in a private local registry.

## Canonical home deployment

The September 29 layout places reusable core at `{home}/.spipe` and private/local
knowledge at `{home}/spipe`. `{home}/spipe/common` links to `{home}/.spipe`; project
`.spipe/common` links through that private workspace route. Set `SPIPE_HOME`
to override core and `SPIPE_WORKSPACE` to override the private workspace.
Keep these roots distinct, including when either is a symlink.

```text
{home}/.spipe/                 reusable SPipe core checkout
{home}/spipe/                  private/local workspace
├── common -> {home}/.spipe
├── companies/            authorized company and organization knowledge
├── projects/             independent project registrations
├── users/                personal knowledge and private mount paths
└── runtime/              local cache, retained state, and active runs
```

`{home}` means the current user's home directory, expanded by the supported
SPipe path options and Simple's `SPIPE_HOME` / `SPIPE_WORKSPACE` wrappers.
Only a leading token is expanded; path contents are never evaluated as code.
Use real checkout-relative executable paths when launching commands.

From an existing core checkout, preview installation and then apply it:

```sh
node scripts/install-spipe.mjs --checkout "{home}/.spipe" --workspace "{home}/spipe"
node scripts/install-spipe.mjs --checkout "{home}/.spipe" --workspace "{home}/spipe" --apply
```

From the core checkout, run `sh scripts/setup-local-knowledge.sh --mode user`
(or `scripts/setup-local-knowledge.ps1 -Mode user`). Setup creates no remote
and uploads no private content. Use the core installer for a new installation.
Existing reversed-layout directories must be inventoried and migrated explicitly;
setup must preserve existing data and reject a conflicting `common` link.
Legacy project submodules remain compatibility routes with their pins intact.

## After cloning a project

Run the host bootstrap:

```sh
SPIPE_HOME="{home}/.spipe" SPIPE_WORKSPACE="{home}/spipe" sh scripts/setup-spipe-local.shs --project example-project
```

On PowerShell, launch from the Simple checkout:

```powershell
$env:SPIPE_HOME = '{home}/.spipe'
$env:SPIPE_WORKSPACE = '{home}/spipe'
./scripts/setup-spipe-local.ps1 -Project example-project
```

The bootstrap
initializes the revision already recorded by the project. Current legacy hosts
with `.spipe/spipe` are supported without moving or overwriting their state.

## Host links and root hook

The reusable SPipe process surfaces are linked into this repository with:

```sh
sh .spipe/common/scripts/setup-spipe-links.sh --dry-run
sh .spipe/common/scripts/setup-spipe-links.sh
```

The Unix setup script follows the configured `host_process_doc` root, matching
the PowerShell setup pattern. In a Simple workspace, it also invokes the host
hook setup to install the root-manifest pre-commit hook when `FILE.md`,
`scripts/setup/setup-hooks.shs`, and `scripts/hooks/pre-commit-root-guard` are
present. A missing prerequisite is reported as a skip rather than changed.
The PowerShell link script currently creates the same documentation links but
does not install that Unix hook; run the host hook setup separately there.

SPipe manuals are Markdown-only under `doc/06_spec/`, mirroring executable
specs after the leading `test/` segment. For example,
`test/03_system/app/spipe/feature/example_spec.spl` maps to
`doc/06_spec/03_system/app/spipe/feature/example_spec.md`. `doc/05_spec` is
not a documentation location in this repository.

The root `scratchpad/` directory is a declared mutable developer-probe area,
not a quarantine location. Keep probes there while they remain local; do not
move it or treat it as quarantine. Mutable quarantine artifacts belong under
`.scv/quarantine/`.

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

The canonical reusable instructions live in the SPipe common checkout under
`doc/00_llm_process/knowledge/` and the `knowledge-ownership` skill.

## Workspace and research integration target

Company content belongs under `companies/<company>/`; departments use its
`organizations/<organization>/`. `projects/<id>/` registers independent project
repositories. Personal knowledge belongs to `users/<user>/`, shared machine
knowledge to `hosts/machines/<host>/`, and private account paths to
`users/<user>/hosts/<host>/mounts.json`. Host defaults/profiles describe desired
setup; runtime probes provide actual capability evidence.

The canonical resolver selects explicit `SPIPE_HOME`, then project `.spipe/common`,
legacy `.spipe/spipe`, `.spipe/spipe_project`, and identified `.spipe` packages.
Home fallbacks are `{home}/.spipe`, `{home}/spipe/common`, legacy `{home}/spipe`,
and legacy `{home}/.spipe/common`, followed by the current identified package.
Project pins retain precedence; route migration never silently upgrades or
removes a recorded submodule.

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
