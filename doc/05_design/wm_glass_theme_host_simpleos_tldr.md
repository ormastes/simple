# WM Glass Theme Detail Design — TLDR

- Add immutable common `ThemeRenderSnapshot` and typed material/shadow values.
- Derive it from `ResolvedThemePackage`; generate the identical bare-metal
  snapshot through repaired `theme-sync compile-to-spl`.
- Install before first host/QEMU frame and key Web caches by material hash.
- Preserve RGBA, layered shadows, backdrop effects and typography through CSS,
  Draw IR and Engine2D; use explicit solid fallback when needed.

```text
parse+hash -> snapshot -> install -> CSS/scene -> Draw IR -> realized evidence
```

- Hosted refresh is a parent-owned, injected-store sequence: capture once,
  stage revision-free immutable wire, atomically swap exactly
  `(revision, wire_text)`, admit migrated WM/GUI/Web store readers,
  `ThemeChangedV1`, exact worker envelope/ack, then a frame carrying explicit
  theme revision/hash. Initial revision is `1`; changed revisions are
  consecutive and a documented unchanged no-op consumes none.
