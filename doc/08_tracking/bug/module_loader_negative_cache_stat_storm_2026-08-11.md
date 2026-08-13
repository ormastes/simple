# Module loader negative-cache filesystem stat storm

This is a condensed restoration of the tracking record originally introduced
by commits `08424ed7075` and `eaae2e73dc5`, restated against current source.

## Status
Fixed in the integrated candidate for `compiler_loader_script_crosslang_perf`;
admitted self-hosted syscall and RSS verification remains pending.

## Reproduction
`bin/simple check test/unit/std/standalone_test.spl` took 3.39 s and 200,568
KiB RSS in the original diagnostic run. `strace -c` recorded 260,105 syscalls:
242,736 `statx` calls (93,248 errors) and 8,651 `readlink` calls (8,477
errors). The measured executable was the Rust bootstrap seed, so this is
diagnostic evidence pending self-hosted reproduction.

## Root-cause evidence
The resolver stored unresolved paths as an empty string while lookup interpreted
that empty string as a cache miss, repeating parent/root probes. The current
resolver distinguishes dictionary presence from the cached empty result and
exposes an uncached-resolution counter for focused regression coverage.

## Fix
Both caller-independent and `module|current_file` caches retain successful and
unsuccessful results through the reset generation. Executable regressions prove
one resolution pass for an exact repeated miss, distinct adjacent caller
entries, and reset invalidation.

## Unblock condition
Reproduce on an admitted self-hosted binary and prove at least 90% fewer failed
loader metadata probes with no p95 latency or maximum-RSS regression. The
retained gate compares the historical 101,725 failed `statx`+`readlink` probes
against a maximum of 10,172 on the same workload. Rust-seed evidence is
inadmissible.
