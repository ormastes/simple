# WM Glass Theme Local Research — TLDR

- `aetheric_dark` is the configured package; recent Aqua WM defaults compete
  with it.
- Hosted WM and Simple Web use hard-coded colors instead of resolved package
  semantics.
- RGBA, shadow, and backdrop-blur data are lost before final rendering.
- The canonical QEMU path is `gui_entry_desktop.spl`, not legacy `wm_entry.spl`.
- Existing QEMU pixels are useful but do not prove theme identity or glass
  semantics.

```text
Theme package (authority)
       |
       +--> WM semantic chrome --> SharedWmScene --+
       |                                           +--> Draw IR --> Engine2D
       +--> resolved Web CSS --> computed style ---+
                                                   |
                                       host + canonical QEMU evidence
```
