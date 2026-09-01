# WM Glass Theme Architecture — TLDR

- `ResolvedThemePackage` remains the only authority.
- Host projects it once at startup; SimpleOS imports a drift-checked generated
  `ThemeRenderSnapshot` from the same package.
- WM/Web/Draw IR are adapters; Engine2D owns transient effect material.
- SHA-256 manifest and normalized material hashes prove semantic parity.
- No file reads in frame/input paths and no private/legacy renderer counts.

```text
package -> immutable snapshot -> WM + Web -> Draw IR -> Engine2D
                  |                                  |
                  +---------- parity evidence -------+
```
