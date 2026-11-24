# native-build per-file lane: what the coordinator and the unit workers really hold (2026-11-24)

Status: OPEN (two small leaks fixed in the same change; the large items below are
measured and unfixed). Host: 60 GB, two Stage 3 builds sharing it. Nothing here
was re-run after the change: no build and no compiler rebuild were allowed, and
the spec was not run (`bin/simple` is absent in this clone and
`s2rel4/simple run <spec>` answers `unknown command 'run'`; the MCP test tools
were not tried).

Evidence: `~/.simple/prov/p3r2/build.log{,.r1,.r14}` (release head, compiler
`s2rel4`), `~/.simple/prov/p3h/build.log.0750`, `p3h/coord_rss.trail.*`, and
read-only `/proc/<pid>/{status,smaps}` samples of the live coordinators and
workers.

## M1 — coordinator

### The "4.4-4.6 GB" figure is a high-water mark, not what the coordinator holds

`[shard] ... parent peak=<n> kB` prints `process_peak_rss_kb()` =
`rt_process_hwm_kib` (VmHWM), sampled in `native_build_hir_shard_count`
(`src/app/cli/native_build_main.spl:1039`).

| coordinator | VmHWM | VmRSS while polling | `[heap]` dirty |
|---|---|---|---|
| release head, pid 506845 (p3r2), 21 min in | 4,360,540 kB | 2,108,092 kB | not sampled |
| older source, pid 83538 (p3h), 4 h in | 4,996,152 kB | 2,203,096 kB | 1,875,900 kB |

Both sit at ~2.1 GB. There is no regression between the two sources. The
"1.3-1.7 GB with the older source" samples come from `coord_rss.trail.0028`,
where the same process fell from 2130 MB (19:30) to 1281 MB (20:51) with no
change in what it was doing and then climbed back to 1674 MB by 00:26
(~110 MB/h). The likely cause is the kernel swapping part of it out and back
under memory pressure; that was not confirmed (no swap figure was recorded for
that run), so the climb is unexplained rather than a measured leak.

The peak is reached before any worker exists. Log order in
`p3r2/build.log`: line 2 `[parse-closure] parent_walks=1 selected=1624 ...
scratch=reclaimed`, line 4 first `[shard]` line with `parent peak=-1`, parse
shards, then line 28670 `parent peak=4360540 kB`. The only heavy work the
coordinator does itself is the in-process entry-closure walk,
`native_build_publish_parse_closure_v1`
(`src/app/cli/native_build_parse_closure_owner.spl:282-358`), reached from
`native_build_closure_ensure_published_for_shards_v1`
(`native_build_main.spl:3152`). Its scratch scope and session are retired and
`rt_session_heap_end` calls `malloc_trim(0)`
(`src/runtime/runtime_native.c:3784`), which is why RSS falls from 4.4 GB to
2.1 GB. What stays is ~1.9 GB of dirty brk heap (first trail sample, before the
walk: 229-281 MB; next sample five minutes later: 2084-2092 MB).

After dispatch the coordinator needs only argv, the ledger directories, the pid
tables and (in `run_file_worker_pool_v1`) the selected-scope path/digest table
for the incremental receipt. None of that should be 1.9 GB.

Not attributed: the residue was not split between the closure walk (allocations
outside its scratch scope and session) and what `run_file_worker_pool_v1` builds
before polling (`compiler_source_authority_selected_scope_v1`,
`file_worker_inc_prepare_v1`). Sampling VmRSS right after the
`[parse-closure] ... scratch=reclaimed` line and again at `[file-worker]
workers=` would settle it.

Not fixed here. If the walk is the owner, running it in a child process (it
already communicates only through the request file and four environment
values) removes both the 4.4 GB peak and the residue. That changes process
structure on the bootstrap path and cannot be tested without a build.

### The peak did not cost a worker at the budgets that were run

`shard_threads_parent_cap_for` (`src/app/cli/shard_mem_clamp.spl:689`) reserves
`max(parent peak, 40 % of the tree budget)` (`shard_host_budget_floor_kb`,
line 449):

| tree budget | 40 % reserve | parent peak | binding | slots at 6,000,000 kB |
|---|---|---|---|---|
| 25,000,000 kB (`build.log.r1`) | 10,000,000 | 4,642,072 | 40 % rule | 15.0 / 6 = 2 |
| 17,000,000 kB (`build.log`) | 6,800,000 | 4,360,540 | 40 % rule | 10.2 / 6 = 1 |

In this HIR-side cap the peak binds only below an 11.6 GB tree budget. The pool
size is `min(hir_count, mir_parallel)` (`run_file_worker_pool_v1`), and the MIR
side (`native_build_shard_threads` -> `shard_threads_mem_cap` with no parent
peak) does not use the coordinator's peak at all; at 17 GB it was the MIR side
that refused (`hir_workers=1 mir_workers=0`, then the serial degrade). So at
the budgets that were run, shrinking the coordinator's peak would not have
admitted another worker. The reserve rules themselves are a policy question for
the owner and are not changed here.

### `measured worker peak commit` is a host-wide number

`[file-worker] measured worker peak commit=31516716 kB` is
`(pool base headroom - current headroom) / live workers`
(`shard_commit_live_footprint_v1`, `shard_mem_clamp.spl:549`), where headroom is
host `MemAvailable + SwapFree`. With a second build on the host its memory is
charged to this pool's workers. No worker in that log reported more than
12,975 MiB (`[codegen] ... rss_mib=`). The inflated figure feeds
`shard_commit_estimate_kib_v1` (the live spawn gate) and is written to the peak
record for the next run. Not fixed here: it needs a per-tree measurement
(cgroup `memory.current` or per-pid RSS) instead of a host delta.

### Residual poll-loop growth (fixed in this change)

Coordinator RSS grows ~24 MB/h while polling (`coord_rss.trail.171728`:
2092 MB at 15:05 -> 2137 MB at 17:00; `coord_rss.trail.0028`: 2084 -> 2130 MB
in 115 min). PR #11002 measured ~13 KB of unreclaimed garbage per
`/proc/meminfo` probe (1.3 MB/s at ~100 probes/s: one 1671-byte read and two
row splits) and moved the probe from every 10 ms round to once a second. The
per-probe garbage was left as it was: 13 KB/s is ~47 MB/h, the same order as
the trails. That the split rows are not released is taken from that
measurement; the runtime free paths were not read for this record.

- `proc_status_kib` (`src/lib/nogc_sync_mut/sffi/process_memory.spl`) now
  decodes the row in place and allocates nothing.
- The spawn gate in `run_ledger_shards` evaluated
  `hir_shard_recovery_blocked(queue_dir)` (formats `"{queue}/BLOCKED"`) before
  the arithmetic admission check, so a free slot that admission kept refusing
  formatted that path every 10 ms. The two conditions are swapped.

Still allocated per probe: the `/proc/meminfo` text itself (~1.5 KB/s) and the
`live_private` array.

## M2 — unit workers

### RSS tracks the unit's HIR import closure, with a ~4.3 GB floor

The launch scripts set `SIMPLE_UNIT_TLDR_IMPORTS=0`, so every unit child takes
the closure-walk route in
`src/compiler/80.driver/driver_source_parse_streaming.spl:682-722` and loads
HIR for the whole frozen import closure of its 8 targets
(`[file-worker] mir-child hir closure modules=<n> of=2157`). The interface-only
arm for those rows, `SIMPLE_FILE_WORKER_INTERFACE_HIR=1`
(`driver_mir_shard_hir_residency_v1.spl:95`, used at
`driver_hir_pipeline_lowering.spl:1503-1508`), is opt-in and was unset in the
worker environment, so every closure row is loaded with bodies.

Serial worker run (`p3r2/build.log.r14`, one worker, exact pairs):

| closure modules | targets | end-of-unit `rss_mib` |
|---|---|---|
| 8, 10, 14, 15, 16 | 6-8 | 4340, 4369, 4356, 4334, 4349 |
| 70, 70, 70, 71 | 4-8 | 4534, 4510, 4538, 4525 |

Flat across 4-8 targets at equal closure size; +~180 MB for +57 closure
modules (~3 MB per module).

Four-worker run (`p3h/build.log.0750`, 195 units; lines interleave, so only the
distributions are comparable):

| quantile | min | p25 | p50 | p75 | p90 | max |
|---|---|---|---|---|---|---|
| closure modules | 8 | 135 | 461 | 578 | 879 | 1574 |
| end-of-unit `rss_mib` | 4243 | 4840 | 6697 | 7582 | 9770 | 12975 |

The top of the RSS list is mostly `compiler.driver.*`, `compiler.mir.*`,
`compiler.types.type_infer.*`: the modules that import most of the compiler.
That is why the late units are the expensive ones.

Not established: per-process pairing for the large closures, and how much of
the growth is in-unit (per-target MIR/codegen garbage) rather than closure
load. Live workers sampled every 3 s do show in-unit growth: one ramped to
3.4 GB in 30 s, held 3.4-3.6 GB for ~70 s, then stepped 3.8 / 4.3 / 4.5 / 4.9 GB
over the next two minutes; another grew 5.8 -> 7.6 GB over 3.5 minutes in small
steps. Those steps were not tied to module boundaries (the samples carry no log
position), so a row-by-row HIR load and a per-module leak both remain open.

### Next step (not done: flag is documented as unmeasured)

A/B one late unit, same batch, per `doc/05_design/compiler/perf/mir_shard_hir_residency_v1.md`:
unset vs `SIMPLE_FILE_WORKER_INTERFACE_HIR=1`; compare `[codegen] ... rss_mib=`
and the object bytes. To separate the two hypotheses above, log `rss_mib` at
`[file-worker] mir-child hir closure` time as well as at the end of the unit.
