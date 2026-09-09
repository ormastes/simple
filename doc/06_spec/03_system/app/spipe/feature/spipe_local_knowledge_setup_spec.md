# SPipe local knowledge setup

The next compatibility revision extends the installed common/organization/project
layout with distinct company, user, and host knowledge scopes. Each
knowledge-owning scope exposes a root index and lazily created `raw`, `wiki`,
`doc`, and `skills` surfaces with their own indexes when present.
Research composes authorized scopes deterministically and treats
`runtime/<user>/<host>/cache` as reconstructible while retaining `state` history
and resumable runs and protecting live `run` files. The executable scenarios
for these additions remain planned; this manual does not claim they pass yet.

**Executable evidence:**
`test/03_system/app/spipe/feature/spipe_local_knowledge_setup_contract_test.shs`

## Create a personal SPipe repository

The user initializer creates an outer user-owned `.spipe` Git repository and
an inner `.spipe` common gitlink in the existing compatibility mode.
The September 9 target uses canonical `~/spipe`, a private `~/.spipe` workspace
with a common link, and Simple's `.spipe/common` route to that checkout. Company,
department, project, user, host, and account-specific mount paths have separate
owners. This target remains planned until integrated execution evidence exists.

## Connect common knowledge

The common checkout is pinned by Git. Running setup again preserves its commit
and does not duplicate scope registrations.

## Set up a cloned project

The project bootstrap initializes the common revision already recorded by the
clone and registers the exact checkout in machine-local configuration. It also
recognizes the legacy `.spipe/spipe` layout without moving dirty state.
The latest locator target prefers project `.spipe/common` and `~/spipe`; legacy
project submodules remain migration fallbacks. Existing revision requirements
must match the selected checkout or yield an explicit incompatibility result.

## Update owner-approved knowledge

Authors choose common, company, organization, project, user, or host ownership,
update the smallest
canonical artifact, and refresh dependent indexes. Rebalancing and common
publication remain reviewed proposal operations.

## Planned workspace acceptance

Plan-only setup performs no writes or network calls. Repeated setup preserves
authored preferences and pins; project registration leaves its source tree
unchanged. Authorized research enters indexes and selected leaves, then follows
normative/evidence references. Cache refresh preserves retained run history.
Company membership does not disclose sibling-department knowledge. Migration
requires reviewed ownership, content hashes and recoverable operations.

The separately supplied Node package's reported 25 fixture tests are research
input, not evidence for the executable path above. CLI/MCP schema-2 integration,
native-platform behavior, shared locator parity, and migration recovery remain
acceptance work recorded in the companion system-test plan.
