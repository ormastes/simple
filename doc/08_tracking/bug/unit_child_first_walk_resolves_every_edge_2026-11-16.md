# Phase 3 emits 0 objects: each unit child's first admitted-graph walk resolves every edge (2026-11-16)

Status: verification-pending (default ON in Wave C1; native wall-time/RSS pending)

## Symptom
Phase 3 of the full CLI ran with stage2 `p3mir/stage2.exe`, which includes #9578, and the `p3_wa2.ps1` OFF lane. It ran 51 minutes at 8 threads with an 8.2 GB tree and produced **0 objects**. The host memory floor then killed it. The owner rule is that the first object must appear within 10 s.

## Evidence (`scratchpad/stagedeploy/`)
- **The coordinator did not loop.** `p3_off.log` has 7 `[coordinator-route]` lines:
  - 1 from the coordinator;
  - 4 from parse-shard children;
  - 2 from file-worker unit children.

  Each child re-enters the CLI and prints the banner plus two `[parse-closure] reused` lines.
- **Timeline from file mtimes:**

  | Time | Event |
  |---|---|
  | 09:31:53 | Coordinator starts |
  | 09:38:58 | Closure request written (a 7-minute walk) |
  | 09:43 to 09:49 | Parse-shard `.fpc` files written (3747) |
  | 09:49:46 | `queue-87584-0` and `mir-queue-87584-0` created |
  | 09:51:22 | Last log line, from the unit children starting |
  | 10:22:55 | Cap kill |
- **Both ledger directories were still empty at the kill.** They held no `.lock`, `.pick`, `.claim`, `inventory` or `unit_order.idx`. The two unit children spent more than 31 minutes before their first ledger write. The first ledger write is `worker_unit_pick_v1`'s `file_lock`.
- In unit mode, the only work before that pick is the source load plus `worker_admitted_edges_v1` over all 3747 seeds (`driver_source_parse_streaming.spl`, `unit_admitted_graph_v1`). Each edge runs `driver_library_mode_resolve_v1` plus `driver_library_mode_native_owner_v1`. Under an admitted epoch, that owner check re-reads the target's bytes on every access.
- **Superlinear scaling.** A seed-interpreted probe over real compiler sources gave N=20 → 56.9 s (6 edges) and N=80 → 441.6 s (99 edges). That is 7.8x the time for 4x the sources.

## Root cause
Every per-file unit child, including the first, runs the whole-inventory admitted-graph walk before it can pick a module. In that walk, every import edge pays an uncached resolve plus a native-owner check, even when a sibling in the same directory has just resolved the same spelling. The first object therefore waits for one full walk, and that walk is over 31 minutes natively at 3747 modules. With batch=1, each later round repeats the walk unless `SIMPLE_UNIT_ORDER_INDEX=1` is set (bug `unit_child_admission_scans_whole_closure_2026-11-15`).

## Fix (default ON as of 2026-11-18 Wave C1; `SIMPLE_WORKER_ADMITTED_MEMO=0`/`false`/`off` rollback)
`worker_admitted_edges_selected_v1` memoizes outcomes per `(candidate, importer dir[, logical owner in a library mode])` within one walk:
- Only Found+admitted (the dep index) and Missing are memoized. Every outcome that carries error text is recomputed.
- Memo rows are promoted out of the per-source transient scope and enter the Dict only after that scope ends.
- The new counter `worker_admitted_resolutions_v1` is exposed.
- Wave C1 (2026-11-18):
  - Flipped `worker_admitted_memo_enabled_v1` and `unit_order_index_enabled_v1` to default ON (`0`/`false`/`off` opt-out rollback).
  - Rewrote `worker_admitted_order_v1` with an explicit `sp` stack pointer over in-place `stack`/`next` arrays (zero `.slice()` allocations on pop).
  - Added advisory `{queue}/.pick_cursor` under `{queue}/.lock` in `worker_unit_pick_v1` (`[cursor .. order.len())` scan, wrapping to `[0 .. cursor)` only when `picked.len() < batch`).

Spec: `test/01_unit/compiler/driver/worker_admitted_memo_spec.spl`, `test/01_unit/compiler/driver/unit_order_index_spec.spl`.
- One directory with 12 importers: 24 resolutions, down to 2 (default ON vs `0` rollback).
- Two directories: 12 resolutions, down to 4.
- Edges and errors are identical with the memo on and off.
- In-place DFS post-order verified on chains, diamond DAGs, disconnected roots, and cycles; `.pick_cursor` progression, dead-owner reclamation wrap-around, and drained proof verified.

RED was recorded on the base (3/3 failed) and GREEN with the fix (3/3 passed; Wave C1 updated specs pass).

## Rollback / Diagnostic Flags (`p3_wa2.ps1`)
```
# Both switches are now default ON; set "0" only to roll back for A/B comparison:
# $env:SIMPLE_WORKER_ADMITTED_MEMO = "0"
# $env:SIMPLE_UNIT_ORDER_INDEX = "0"
# fallback if the first walk is still too slow: the old two-pass route
$env:SIMPLE_FILE_WORKERS = "0"
$env:SIMPLE_COMPILER_PHASE_PROFILE = "1"  # admitted-graph progress lines every 128 sources
```

## Still open
- The first unit still runs the full walk (now memoized by default). Concurrent first units each walk too, because the order index has no single-flight. The coordinator's own 7-minute closure walk is not reused by the children.
- Resolved in Wave C1 (2026-11-18): `worker_admitted_order_v1` no longer copies `stack.slice`/`next.slice` on pop (in-place `sp` stack), and `worker_unit_pick_v1` maintains `{queue}/.pick_cursor` instead of rescanning `order` from `0` on every pick.
- Not measured:
  - native wall time and RSS, before and after;
  - phase 3 and stage2, which were not run in this lane;
  - the reduction ratio on the real inventory, which depends on how many importers share a directory.
