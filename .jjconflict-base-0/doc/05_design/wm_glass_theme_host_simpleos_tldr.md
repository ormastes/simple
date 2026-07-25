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
