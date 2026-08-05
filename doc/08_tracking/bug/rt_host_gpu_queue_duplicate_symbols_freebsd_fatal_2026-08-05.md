# `rt_host_gpu_queue_*` duplicated between C and Rust — fatal under FreeBSD's `lld`

**Found by:** Lane B (FreeBSD WM seam), 2026-08-05, while trying to link
`simple-runtime` inside a real FreeBSD 14.4-RELEASE QEMU guest per
`.claude/rules/board-runnable.md`. Board-run is currently **blocked** by this
defect, not by anything in Lane B's own scope (`src/os/compositor/`,
`src/lib/nogc_async_mut/wm/`).

## The defect

Five symbols are defined **twice**, once in C and once in Rust, both `extern
"C"`-linked into the same `simple-runtime` staticlib:

| symbol | C definition | Rust definition |
|---|---|---|
| `rt_host_gpu_queue_complete` | `src/runtime/runtime_native.c:716` | `src/compiler_rust/runtime/src/host_gpu_lane.rs:290` |
| `rt_host_gpu_queue_drain` | `runtime_native.c:734` | `host_gpu_lane.rs:310` |
| `rt_host_gpu_queue_packet_count` | `runtime_native.c:777` | `host_gpu_lane.rs:337` |
| `rt_host_gpu_queue_submitted_count` | `runtime_native.c:778` | `host_gpu_lane.rs:342` |
| `rt_host_gpu_queue_completed_count` | `runtime_native.c:779` | `host_gpu_lane.rs:347` |

Both sides implement independent, non-trivial queue state (separate static
counters/backing storage on each side) — this is not a stale stub that can be
deleted without checking which copy callers actually need live.

## Why it was invisible until now

GNU `ld` (the default linker on this Linux dev host) tolerates duplicate
strong symbol definitions across translation units in a way FreeBSD's default
`lld` does not — same shape as
[[reference_muldefs_makes_duplicate_symbols_silent_not_fatal]]. `cargo build
-p simple-runtime` links clean on Linux; the identical source tree fails at
link time in the FreeBSD guest with `cargo exit=101`, duplicate symbol errors
naming exactly these five names.

## Impact

- FreeBSD `simple-runtime` cannot link at all — blocks every board-runnable
  claim for the WM/GUI/2D lane on FreeBSD (task #60).
- Likely also fatal on any other `lld`/`mold`-default host (macOS `ld64`
  behavior unverified) — worth checking before assuming this is FreeBSD-only.
- Not fatal on the Linux dev host today only because of linker tolerance, not
  because the duplication is safe.

## Suggested fix shape (not yet attempted — needs an owner)

Decide which implementation is the real one (likely `host_gpu_lane.rs`, given
`runtime_native.c`'s copy has no test coverage found by Lane B and the Rust
side carries its own unit tests at `host_gpu_lane.rs:431+`), delete the
losing C copy, and confirm no caller depended on divergent behavior between
the two (same trap as
[[reference_a_fix_labelled_commit_can_be_a_tree_wipe]] — diff both directions
before deleting either side).

## Verification once fixed

Re-run `scripts/check/check-freebsd-wm-seam-refusal.shs` inside the FreeBSD
QEMU guest (`build/freebsd/vm/`, real BASIC-CLOUDINIT boot, KVM accel, no
`-kernel`/`isa-debug-exit`) — it currently exits non-zero with `refusal=blocked
reason=in-guest build did not complete`. A clean link should let it reach the
real `refusal=yes` verdict against the live `wm_host_2d_for("freebsd")` seam.
