# Module loader negative-cache filesystem stat storm

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

On 2026-08-19 the long-lived-session remainder was closed in Pure Simple: the
combined caches are capped at 256 entries, each uncached resolution retains its
bounded file/directory probe dependency set, and explicit create/edit/move/
delete notifications invalidate stale hits and misses. The compiler watcher now
routes added/modified/deleted source events through those notifications, while
its move bridge preserves old and new identities in one invalidation event.
Fast, precise-full, fail-closed-full, ambiguity, event-kind, and changed-path
counts are reported separately. A fast-entry invalidation can therefore no
longer suppress the conservative full-cache clear required by an unmatched
producer path spelling. The focused regression covers 300 unique misses, all
four mutation classes, exact telemetry, and the spelling-mismatch case. The
correctness receipt and still-blocked self-hosted admission are retained in
`doc/10_metrics/compiler/loader_negative_cache_bounded_2026-08-19.md`.

## Unblock condition
Reproduce on an admitted self-hosted binary and prove at least 90% fewer failed
loader metadata probes with no p95 latency or maximum-RSS regression. The
retained gate compares the historical 101,725 failed `statx`+`readlink` probes
against a maximum of 10,172 on the same workload. Rust-seed evidence is
inadmissible.
