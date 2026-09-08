<!-- codex-design -->
# SPipe local knowledge setup detail design

Date: 2026-09-08. Status: implementation contract, refined by Astra.
Requirements: [architecture](../04_architecture/spipe_local_knowledge_setup.md).

## Shared interfaces

`SetupRequest` records mode (`user` or `project`), destination, selected common
repository and revision, optional organization identity, and project identity.
`SetupInspection` records existing Git root, target occupancy, common gitlink,
dirty paths in the target, and recognized legacy layout. `SetupPlan` contains
exact owned paths and ordered operations. `SetupReceipt` records completed
operations, effective revision, local registry location, and unresolved actions.

`inspect_setup(request) -> inspection`, `plan_setup(request, inspection) -> plan`,
and `apply_setup(plan) -> receipt` are design contracts, not claims of existing
exports. The interactive entrypoint and deterministic test path share the same
validation and application logic. Use existing SPipe records and resolver APIs
when their implementation already provides these roles.

## Interactive behavior

1. Identify first-user installation or project-clone setup.
2. Prompt for destination, displaying the resolved `.spipe` path.
3. Inspect Git state and identify an existing matching common submodule.
4. Select common source/revision; retain an existing project pin by default.
5. Offer optional organization registration and project registration.
6. Show directories, submodule operations, and tracked versus local outputs.
7. Apply the selected changes, then print the receipt and relevant guide paths.

EOF/cancellation before application exits without changes. Noninteractive
invocations require explicit mode and necessary values; they never hang on
stdin. Avoid interpreting supplied paths or repository arguments as shell code.
The first-user path may initialize a local repository, but must not invent a
remote or publish content. Project-clone setup initializes its recorded
submodule and registers the checkout without inventing a replacement pin.

## Files and state

| Data | Storage rule |
|---|---|
| Common dependency | Git submodule/gitlink and shareable revision lock. |
| Project identity/dependencies | Existing project manifest or compatible `.spipe/projects.sdn` resolver. |
| Absolute local checkout paths | Ignored user-local registry, outside the common submodule. |
| Organization/project knowledge | Owner-selected canonical root or registered existing checkout. |
| Setup receipt/cache | Ignored local state, excluding credentials. |

Never create mutable project registry files inside a read-only common checkout.
For the direct project `.spipe` submodule layout, migrate the resolver's physical
storage through an explicit compatibility adapter; do not silently create a
second independent registry. A legacy `.spipe/projects.sdn` is imported or
resolved in place only after format and ownership validation.

Validate path containment and aliases before mutation; reject self-nesting,
symlink escapes, another repository's Git administrative directories, and
occupied unrelated targets. Use a temporary sibling file plus atomic rename for
new local metadata. Git commands may leave recoverable partial state: report it
precisely and support resuming, rather than deleting pre-existing directories.

## Content and authoring contract

Every traversable scope/wiki directory has one `index.md` with stable must-know
content, child routes, evidence groups, and exceptions. Existing `README.md`
files may remain. Preserve native `SKILL.md` and agent-definition filenames.
Indexes link to lifecycle documents and do not become second writable copies.

The guide and skill teach this flow: resolve scope and authorization; read the
node index and source evidence; propose the smallest canonical change; validate
identity, references, applicability, and confidentiality; apply an owner-approved
change; refresh only dependent navigation/summaries. Research results and
durable wiki changes have separate review states.

Company content belongs in organization scope; project architecture, tests, and
incidents stay with their project. A common contribution is reviewed and
sanitized, receives a new identity when crossing scopes, and does not expose
private paths or internal provenance. Rebalancing starts with a proposal;
physical moves and cross-scope publication do not follow from popularity.

## Errors and recovery

Errors distinguish missing Git, unavailable source, invalid revision, occupied
target, wrong submodule identity, legacy layout requiring migration, permission
failure, and interrupted application. A second identical setup preserves
existing file bytes and revision pins. A network failure reports its completed
local operations and next recoverable step; it does not claim completion.

## Deferred boundaries

Provider launchers, DFS execution, telemetry, learned grouping, and KV reuse are
later waves. The setup guide may describe those contracts as planned; it must
not expose an unimplemented command as working or assert a provider cache hit.
