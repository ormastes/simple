# Simple mmap Preload Size Gap

Date: 2026-05-27
Status: RESOLVED (verified 2026-05-29)

## Summary

The startup/size audit now has a working Simple-side mmap preload lane that is
below the C counter-size target on the audited Linux host.

Current evidence from:

```sh
sh scripts/check-startup-size-performance-audit.shs
```

Current measured rows:

- C mmap preload argparse: `14472` bytes, runs successfully.
- Simple mmap preload argparse: `14400` bytes, runs successfully.
- Simple mmap loaded libraries: `libc.so.6` and `/lib64/ld-linux-x86-64.so.2`.
- SimpleOS VFS counterpart: `VfsManager.preload_file_pages(path, page_size)`
  warms the filesystem/block-cache path and returns pages touched.

## Gap

The audited Simple lane is currently `72` bytes smaller than the C mmap+argparse
counter. It parses `-f <path>` from argv and preloads through the core-C runtime
lane without extra loaded libraries or heavy markers.

Previous Simple evidence was `34968` bytes through `simple-core`; moving the
audit probe to core-C, removing the broad bootstrap runtime object, splitting
the MCP fast path out of `runtime_native.c`, and compiling core-C objects for
size reduced the row by `20568` bytes.

## Likely Fix Direction

- Keep mmap/preload in the core-C startup lane and do not pull in hosted
  runtime, regex, CLI, parser, or full `simple-core` modules for this probe.
- Keep the SimpleOS VFS preload contract path-based so filesystems backed by
  `BlockCache` warm through ordinary reads without exposing sector layout at
  the VFS layer.
- Keep a regression gate around this row because small linker/runtime retention
  changes can easily push it back above the C counter.
- Investigate a thinner runtime-free or syscall-oriented lane only if future
  targets require beating the asm baseline rather than matching C.

## Resolution

All items above are implemented and verified as of 2026-05-29:

- `src/runtime/simple_core/core_fs.spl` provides `pub fn rt_file_preload_pages(path: i64) -> i64`
  using `open` + `lseek` + `mmap` + page-touch loop + `munmap` — no hosted runtime, no regex,
  no CLI/parser modules.
- `scripts/check-startup-size-performance-audit.shs` builds `simple_mmap_preload` using
  `--runtime-bundle core-c-bootstrap` from a minimal entry `.spl` that declares only
  `rt_cli_get_args` and `rt_file_preload_pages` as externs.
- Regression gate `check_mmap_preload_gate` is active at the end of the script; it fails the
  audit run if Simple bytes exceed the C counter bytes.
- Verified loaded libraries: `libc.so.6` and `/lib64/ld-linux-x86-64.so.2` only — no
  TLS/compression/regex stacks.
- Audit report (`doc/09_report/startup_size_performance_audit_2026-05-27.md`, run 2026-05-29):
  - C mmap preload argparse: **14472 bytes**, status ok
  - Simple mmap preload argparse: **14400 bytes**, status ok
  - Gap: Simple is **72 bytes smaller** than C counter — gate passes.
- SimpleOS VFS counterpart `VfsManager.preload_file_pages(path, page_size)` keeps the contract
  path-based, warming block-cache without exposing sector layout at VFS layer.
