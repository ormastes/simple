# WM browser event production-envelope state

## Implemented source-only admission

- Event evidence now consumes canonical Aetheric production HTML retained by
  `aetheric-host-web-gui-v1`; it no longer builds a parallel fixed light theme.
- The wrapper validates the production envelope before any Electron command.
- The proof validator binds the HTML hash, snapshot fingerprints, computed glass
  witnesses, and non-synthetic/non-compatibility flags.

## Deliberate execution boundary

No browser, native GUI, QEMU, or capture process was launched for this change.
Live admission still requires existing qualifying Aetheric production proof and
the normal Electron/font evidence prerequisites.
