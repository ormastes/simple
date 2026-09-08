# SPipe local knowledge setup

**Executable evidence:**
`test/03_system/app/spipe/feature/spipe_local_knowledge_setup_contract_test.shs`

## Create a personal SPipe repository

The user initializer creates an outer user-owned `.spipe` Git repository and
an inner `.spipe` common gitlink. Organization, project, and machine-local
registry paths remain independently owned.

## Connect common knowledge

The common checkout is pinned by Git. Running setup again preserves its commit
and does not duplicate scope registrations.

## Set up a cloned project

The project bootstrap initializes the common revision already recorded by the
clone and registers the exact checkout in machine-local configuration. It also
recognizes the legacy `.spipe/spipe` layout without moving dirty state.

## Update owner-approved knowledge

Authors choose common, organization, or project ownership, update the smallest
canonical artifact, and refresh dependent indexes. Rebalancing and common
publication remain reviewed proposal operations.
