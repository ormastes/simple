# Agent Tasks: WM Glass Theme on Host and SimpleOS

## Shared Contract

Authority and interfaces are fixed: `ResolvedThemePackage`, derived
`ThemeRenderSnapshot`, existing `SimpleTheme` adapter, `WmChromeColors`,
`SharedWmScene`, `DrawIrComposition`, `Engine2D`, and canonical x86_64
`gui_entry_desktop.spl`. No lane may invent a registry or renderer.

Manual steps and fail-fast text are fixed by the system-test plan. Missing
helpers use `fail("wm glass theme evidence not implemented")` or `assert(false)`.

## Implementation Lanes

1. Package/snapshot lane: typed parsing, SHA-256 manifest/material identity,
   generator and drift checks.
2. WM/bootstrap lane: full projection, hosted startup and canonical SimpleOS
   generated-snapshot installation.
3. Web/Draw IR lane: package CSS wiring, computed-style/accessor repair,
   Engine2D glass lowering and focused regressions.
4. Evidence lane: extend canonical host, GUI/Web parity and QEMU wrappers;
   produce correlated semantic/capability/pixel/performance artifacts.
5. Spec/manual lane: executable SPipe scenarios, docgen, capture links and
   traceability review.

The three read-only design sidecars completed architecture, system-test and
GUI/evidence audits. Further lower-model sidecars may own only bounded lanes
above after checking worktree ownership.

## Ownership

- Merge owner: primary Codex agent in `/root`.
- Broad exclusions/done marks: primary only.
- Generated-manual reviewer: primary normal/highest-capability pass.
- Final production-readiness reviewer: primary highest available model after
  all sidecars finish and changes are merged.

## Merge Order

Package/snapshot -> WM/bootstrap -> Web/Draw IR -> evidence -> spec/manual.
Each lane supplies focused passing tests once; the merge owner resolves shared
types and verifies no concurrent unrelated work was absorbed.
