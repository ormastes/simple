<!-- codex-architecture -->
# SPipe local knowledge setup architecture

Date: 2026-09-08. Status: implementation contract, refined by Astra.
Scope: implement and publish local setup, ownership, navigation, and authoring
guidance before continuing the research-controller and Slang KV-cache waves.
The supplied September 8 SPipe + Slang report is the research input; its provider
and performance claims are historical input, not newly verified measurements.

## Selected requirements

| ID | User-selected outcome |
|---|---|
| REQ-001 | A user-owned `.spipe` repository contains a `.spipe` common submodule, `organization/`, and `projects/`. |
| REQ-002 | Interactive setup supports first installation and use after cloning a project. |
| REQ-003 | Common, organization, and project content retains independent ownership. |
| REQ-004 | Shared configuration contains logical identities and revision pins; local configuration owns machine paths. |
| REQ-005 | Traversable wiki nodes use `index.md`; lifecycle documents remain canonical. |
| REQ-006 | Guides and skills explain reading, updating, rebalancing, and proposing reusable knowledge. |
| REQ-007 | Setup preserves existing repositories, provider instructions, local edits, and unrelated staged work. |
| REQ-008 | Hosted-only operation remains possible; installation has no Slang/model dependency. |

## Ownership and physical layout

```text
<user-root>/.spipe/                 user repository; ~/.spipe is a default
├── .spipe/                        pinned common SPipe Git submodule
├── organization/<organization>/   user-authorized organization content/registration
├── projects/<project>/            project content/registration
└── local/                        ignored machine-specific registry/state
<project-checkout>/
├── .spipe/                        project-pinned common SPipe Git submodule
└── doc/                           existing canonical project documentation
```

The two conceptual names `user_spipe` and `spipe_repo` both become `.spipe` on
disk. Their containment is deliberate: `<user-root>/.spipe/.spipe`. A project
mount selects its own common revision; it must not silently replace that pin
with the user's common checkout. Registered existing organization/project
checkouts remain in place; registration does not copy their contents.

## Components and boundaries

| Component | Responsibility |
|---|---|
| Setup entrypoint | Collect choices, inspect targets, print intended changes, perform bounded initialization. |
| Git adapter | Validate repository identity; add/init only the requested submodule and preserve pins. |
| Scope registry | Resolve identity and local root; extend the existing project resolver. |
| Knowledge navigation | Render `index.md` routes without creating duplicate canonical documents. |
| Authoring guidance | Select owner, capture evidence, propose changes, validate links, update owner-approved content. |

Composition uses narrow adapters and shared records. Cross-cutting policy and
provenance belong in shared contracts, while Git and filesystem details remain
inside setup adapters. No compiler or kernel restructuring is necessary.

Common is the reusable distribution. Organization restrictions remain effective
when composing project skills; registration alone grants no membership or export
authority. Local preferences do not create a fourth canonical knowledge scope.
Provider agent/skill files are integration surfaces with their native filenames.

## Repository compatibility

Inspection found `.gitmodules` registering `.spipe/spipe` at
`https://github.com/ormastes/Spipe.git`; that checkout is dirty. Existing
architecture lives under `doc/04_architecture/infra/spipe/` and
`doc/05_design/infra/spipe/`. This design extends those contracts.

An occupied project `.spipe` directory is a migration case, not an empty target.
The installer must diagnose the legacy nested submodule and preserve it. Moving
it requires a separately reviewed migration that accounts for state, registry
files, Git metadata, and dirty content. Newly created installations use the
requested direct `.spipe` submodule layout immediately.

## Knowledge maintenance and later work

Keep authority, navigation, and prompt packing separate. Rebalance analysis is
read-only by default; physical moves require an owner-approved plan. Common
publication creates a sanitized independent artifact after review. Runtime
ordering may change only with strictly greater than 10% supported improvement
and observation/amortization gates; setup does not implement that optimizer.

Startup probes only selected roots and manifests. Full scans belong to explicit
maintenance. Index invalidation follows changed content/dependencies, while a
common revision update is deliberate. Measure local setup time and subprocess
count on fixtures; exclude network transfer from a fabricated latency promise.

Next: hosted research controller and exact context manifests, then Slang
instrumentation/isolation and serial exact-prefix restore. No cache capability
is claimed by completing this setup phase.
