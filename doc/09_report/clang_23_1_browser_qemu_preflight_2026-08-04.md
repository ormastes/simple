# Clang 23.1 Browser/QEMU Preflight — 2026-08-04

## Scope

Read-only host and static-contract preflight for the isolated
`codex/clang-23-1-browser-demo` worktree. The canonical fullscreen QEMU wrapper
was intentionally not started. Existing migration edits were not modified.

## Result

**STATUS: BLOCKED (provider and executable SSpec evidence pending)**

The host can run the eventual rendering gate. The static SimpleOS x86_64 WM
preflight passed. Full readiness is blocked until the matching LLVM 23.1
provider exists and the stale browser staging assertion is reconciled.

## Passed once

- `scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs`: PASS. It reports
  the production desktop entry, theme ordering, CSS/VFS ordering, SSE2 evidence,
  and correctly leaves live QEMU as `not-started-host-gate`.
- QEMU: `/opt/homebrew/bin/qemu-system-x86_64`, version 10.2.2.
- mtools: `mcopy`, `mformat`, and `mmd` present; mtools version 4.0.49.
- Disk tooling: `/opt/homebrew/bin/qemu-img` present.
- OVMF code: `/opt/homebrew/share/qemu/edk2-x86_64-code.fd`, 3,653,632 bytes,
  SHA-256 `33090cc07675baa5190d9f1e84bf5176b33bcbfa9bacac522961150cdb6dbb2a`.
- OVMF vars: `/opt/homebrew/share/qemu/edk2-i386-vars.fd`, 540,672 bytes,
  SHA-256 `5d2ac383371b408398accee7ec27c8c09ea5b74a0de0ceea6513388b15be5d1e`.
- Pinned font: `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`,
  1,708,408 bytes, SHA-256
  `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`;
  both match the canonical wrapper's oracle.
- Supplied provider: `/Users/ormastes/simple/build/native_probe/simple`, executable,
  version `simple-bootstrap 1.0.0-beta`, SHA-256
  `93480fcc6f062dbe6a80a8f1276fddf235520c36b4d2ef8b8ca4c8c9a4f570c1`.
- Canonical wrapper contains browser `BROWSMF.SMF` staging, QMP
  `input-send-event`, and `pmemsave` evidence paths.

## Concrete blockers

1. No executable Clang 23.1 provider was present at the checked worktree
   locations (`build/toolchains/llvm-23.1.0-rc2`, `build/toolchains/llvm-23.1`,
   or `build/llvm-23.1.0-rc2`). The browser build and full QEMU gate must wait
   for the provider-build lane and then receive explicit matching `CLANG` and
   `LINKER` paths.
2. `test/03_system/check/simpleos_browser_demo_guest_elf_staging_contract_spec.spl`
   requires the builder text to contain `simpleos_syscall.S`, but
   `scripts/os/build_browser_demo_client.shs` does not contain that reference.
   This is a static contract mismatch to resolve before accepting that spec.
3. The supplied bootstrap provider exposes no `test` command. The repository
   pure-Simple binary started the SSpec runner but failed before execution with
   unresolved `describe`, `it`, `step`, and `expect` after reporting its seed
   sibling unavailable. Consequently the three SSpec files were not marked
   PASS; this is runner/tooling evidence debt, not a QEMU host prerequisite
   failure.

## Next canonical gate

After blockers 1–3 are resolved, run exactly once with explicit admitted tools:

```sh
SIMPLE_BIN=/Users/ormastes/simple/build/native_probe/simple \
CLANG=<llvm-23.1-prefix>/bin/clang \
LINKER=<llvm-23.1-prefix>/bin/ld.lld \
BUILD_DIR=<isolated-build-dir> \
REPORT_PATH=<isolated-report-path> \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

That remaining operation must prove the browser ELF build and byte-identical
guest staging before the retained rendering/input evidence can converge.
