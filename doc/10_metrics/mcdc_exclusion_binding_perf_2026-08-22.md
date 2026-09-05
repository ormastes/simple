# MC/DC exclusion binding performance evidence — 2026-08-22

Command: `sh scripts/check/check-mcdc-native-runtime-perf.shs` on the same
worktree and host, once before and once after the binding change.

| Revision state | Wall time | Driver peak RSS |
|---|---:|---:|
| before | 5.56 s | 47,652 KiB |
| after | 4.16 s | 47,736 KiB |

The 84 KiB RSS delta (0.18%) is below process/compiler noise; elapsed time did
not regress. The retained after artifact reports 5,092 ns/report, 0 allocations,
512 workspace bytes, and 9,472 KiB runtime peak RSS. Source binding is offline:
one ordered O(N) pass, at most 256 fixed 376-byte rows, a bounded scenario hash
index, and no probe/runtime hot-path dispatch or allocation.

The canonical optimizer command was attempted once but the worktree has no
`bin/simple` entrypoint; the separately deployed self-hosted binary remains
inadmissible for this source revision. The Rust seed was not substituted. Focused native self-check and
performance evidence passed; no broad build was run.
