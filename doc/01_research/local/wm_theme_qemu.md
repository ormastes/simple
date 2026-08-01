<!-- codex-research -->
# WM theme + QEMU local research

## Current implementation

- `apply_wm_css_theme_text()` parses the six `--wm-*` tokens and, when a
  baseline snapshot exists, derives an effective snapshot before registering
  exact chrome-only values. The hosted entry re-reads that snapshot before it
  creates the theme install wire and backend.
- x86_64, AArch64, and RISC-V desktop entries install their generated baseline,
  mount VFS, read `/THEME.CSS`, and call the shared override before creating
  the first frame executor. This is source evidence, not a guest proof.
- The 2026-08-01 cache repair made BrowserBackend and normal Simple Web content
  revisions material-aware. Review then found two unresolved AC-4 gaps:
  effective snapshots retained old `composed_css`, and the hosted receipt
  revision mixed source manifest but not material.
- Native hosted Cranelift has a known Option aggregate ABI defect for
  `active_wm_theme_render_snapshot()`. Consumers need scalar accessors or a
  presence guard plus `active_wm_theme_snapshot_unchecked()`.

## QEMU evidence status

| Target | Source order | Live visual/input proof | Blocking prerequisite |
|---|---|---|---|
| x86_64 | wired | not admissible | VirtIO serial transport, then current desktop artifact and capture |
| AArch64 | wired | not admissible | attested ELF/FAT/manifest and physical Cocoa interaction evidence |
| RISC-V | wired | blocked | VirtIO serial transport |

Authoritative live evidence/resume ownership is
`doc/03_plan/sys_test/simpleos_qemu_wm_real_screen.md`.

## History

- `0453d4fa8f` added guarded VFS ordering for `/THEME.CSS`.
- `9892b6f51f` propagated override-derived snapshot identity through hosted
  wire/backend and cache paths.
- The follow-up source review established that identity-only coverage cannot
  prove Web CSS pixels; CSS materialization and receipt revision remain active.
