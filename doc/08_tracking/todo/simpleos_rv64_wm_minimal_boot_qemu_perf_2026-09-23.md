# RV64 WM minimal-boot deferred QEMU and resource verification

Status: deferred until the Linux bootstrap phase provides an admitted compiler
and the RV64 QEMU phase is enabled.

The source-level fix removes the duplicate constant-true WM row and narrows
boot-source discovery without dropping the legacy
`baremetal_runtime_core.inc.c` translation-unit owner. Lightweight regression
coverage pins both properties, but it is not guest evidence.

Run from a clean worktree with no other compiler or QEMU workload:

```sh
/usr/bin/time -v env JOBS=12 BOOT_WAIT=420 \
  SIMPLE_BIN=<admitted-phase-binary> \
  sh scripts/check/check-simpleos-riscv64-wm-render-smoke-opensbi.shs
```

Acceptance requires a fresh nonce-correlated serial and pixel PASS, no weak or
undefined runtime symbols, the exact admitted compiler hash in the retained
receipt, elapsed boot within the existing 420-second deadline, and peak host
RSS below 16 GiB. Also compare elapsed time and peak RSS with the last admitted
RV64 WM receipt; a regression above 10% requires diagnosis rather than
promotion. Retain `/usr/bin/time -v` output, kernel/firmware hashes, QEMU argv,
serial log, QMP log, and screendump.
