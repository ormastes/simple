# Robust lint lane scan exceeds bounded verification time

Status: Open

After repairing split profile parsing and lint admission, running robust lint
over `src/lib/nogc_async_mut` produced no terminal verdict or filtered SFFI
diagnostic within 120 seconds and was stopped. Per-file robust checks terminate,
so the defect is in directory-scale discovery/execution rather than SFFI009 or
SFFI010 semantics.

The migration workaround is the source-only SFFI call-authority census. It
scans the complete owned source/test tree in 24.21 seconds with 7,424 KiB peak
RSS and supports a fail-on-missing gate. It is deliberately not called from a
runtime hot path.

Required fix: profile directory lint with phase timings, reuse parsed/compiler
state across files, avoid repeated module loading, and add a realistic warm
latency/RSS release gate. Do not weaken or skip AST lints to meet the target.


---

## Lane disposition 2026-11-13 (p3-misc-b)

open scan-latency item per in-file status (no terminal verdict produced); owner: robust-lint lane.
---

## Lane disposition 2026-11-13 (live-p3-l4, work/live-p3-l4-20261113, base f790f7f266e)

Concurs with p3-misc-b: the recorded required fix (phase timings, cross-file compiler-state reuse, avoiding repeated module loading, warm latency/RSS release gate) is a lint-lane performance program, and the migration workaround (source-only SFFI call-authority census, 24.21 s / 7.4 MiB over the whole tree) remains the honest fallback. Profiling directory-scale lint on this Windows interpreter host would produce numbers no one can gate on. No in-lane change. Owner: robust-lint lane.
