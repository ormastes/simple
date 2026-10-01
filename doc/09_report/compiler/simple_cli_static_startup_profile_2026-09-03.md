# Simple CLI static startup profile — macOS arm64

**Date:** 2026-09-03
**Host:** macOS arm64
**Source revision:** `06aa9ab732c16206b82f5e411cfd48794ae9e2a6`
**Admitted binary:** `/Users/ormastes/simple/bin/release/macos-arm64/simple`
**SHA-256:** `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`

## Baseline

Five process samples per command with `/usr/bin/time -lp` measured both exact
`--version` and exact `--help` at 0.03 seconds mean wall time. The observed
maximum resident set size was 10,829,824 bytes (10.33 MiB). The executable is
24 MiB on disk, with 14.1 MiB `__TEXT`, 9.0 MiB `__LINKEDIT`, and only about
22 KiB writable zero-fill data. Mach-O's normal 4 GiB `__PAGEZERO` reservation
is virtual guard space, not resident storage.

The binary links AppKit, Foundation, CoreServices, IOKit, SystemConfiguration,
Security, CoreFoundation, libc++, and libSystem. Nine explicit Simple module
initializers are present. No runtime directory scan appears in the exact
command source path.

## Finding and optimization

`main()` validated K1 policy, built and installed the selected backend table,
constructed and merged thirteen optional static backend entries, then parsed
general logging/runtime flags before recognizing exact help or version.

The optimized path still validates the selected/requested K1 policy and still
honors required Phase-7 child instrumentation. For an ordinary exact `-h`,
`--help`, `-v`, or `--version`, it now prints and exits before backend table
construction, global option parsing, fault setup, JIT environment mutation,
memory-infrastructure resolution, argument filtering, and provider activation.
Option-bearing requests such as `--json --version` retain the full path.

## Evidence

- Behavioral classifier: 3/3 focused SPipe scenarios passed.
- Source-order performance contract: 2/2 focused SPipe scenarios passed.
- Optimizer invocation was attempted twice, including forced interpreter mode;
  the admitted executable returned exit 1 with only
  `[STDERR] Error running src/app/optimize/main.spl`. No optimizer success is
  claimed.
- A trustworthy after-runtime number is unavailable because the admitted
  binary predates this source patch and no producer-authenticated rebuilt full
  CLI is available. Source-order evidence proves removal of the work but is not
  reported as a measured latency improvement.

## Follow-up opportunity

The exact command still pays for the monolithic full-CLI link closure and its
platform frameworks before `main()`. A future entry-closure split could make a
small static CLI-0 executable for help/version and delegate product commands,
but that is an architectural packaging change and was intentionally not mixed
into this semantics-preserving optimization.
