# Layout Framework Agent Tasks — TLDR

- Contracts, profiles, scheduler, execution ports, browser CPU/GPU ports, and evidence use disjoint files.
- Root Codex is merge owner and final reviewer.
- Shared interfaces and four manual steps are frozen before implementation.
- Shared browser renderer edits are serial and owned by the merge owner.

<!-- sdn-diagram:id=layout-framework-agent-tasks-tldr -->
```sdn
team: {parallel: [contracts, profiles, scheduler, execution, browser_ports, evidence], merge: root, review: root}
```
