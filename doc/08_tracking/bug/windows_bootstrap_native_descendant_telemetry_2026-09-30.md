# Windows bootstrap progress misses native descendants

Status: open; observation received from the recovery owner, not reproduced by
this source-only startup/cache lane. No evidence of an actual stalled build.

During the frozen Windows recovery run on 2026-09-30, Rust/runtime stages
reported real PASS while the outer MSYS progress monitor showed quiet or low
tree CPU and increasing `stall_streak`. Native Windows `rustc`/`clang`
descendants may be absent from the MSYS process inventory used by
`scripts/bootstrap/bootstrap-progress-watch.shs`.

Reproducer: launch a bounded native Windows CPU worker as a child of a Git Bash
wrapper, retain its Windows PID and creation time, and sample both the monitor
and native Windows process inventory. Compare descendant membership and CPU
time deltas while the native worker demonstrably runs. Preserve both raw
samples with the wrapper identity and exit result; a quiet log alone is not
proof of a stall.

Prevention test plan: cover direct and nested native descendants, PID reuse,
exited descendants, unrelated workers, inaccessible processes and mixed MSYS /
native chains. Require CPU aggregation to include only descendants matching
stable process identities. Missing inventory must report incomplete telemetry,
not assert that the build is idle. Verify terminal stage evidence still wins
over observational stall classification. Keep tests in disposable process
trees; do not restart or instrument the live recovery build.

This record does not change RSS limits, worker scheduling, cache authority,
stage admission or restart policy. Runtime host access must use SOSIX-owned
facades; shell bootstrap observation remains owned by the bootstrap monitor.
