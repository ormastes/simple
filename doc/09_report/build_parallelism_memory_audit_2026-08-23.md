# Build parallelism and worker memory footprint — audit

- Date: 2026-08-23
- Base: `origin/main` @ `e1f31f31da9`
- Method: **observational only.** No build was started by this lane (the box was
  at load 51 with 15 GB free). All numbers come from read-only `/proc` sampling
  of 41 `native_build_worker` processes already running in two other lanes
  (521 samples / 10 s interval / ~9 min), plus source reading. Sampler:
  `/mnt/fast/parallel-audit/sample.sh`, raw data `rss_timeseries.tsv`.

## 1. Where a worker's ~2.5-3 GB actually goes

Snapshot, `/proc/<pid>/smaps` + `smaps_rollup` + `status` of one worker:

| line | value |
|---|---|
| `VmRSS` | 2 530 364 kB (2.41 GB) |
| `VmPeak` / `VmSize` | 3 530 080 kB (3.37 GB) |
| `VmData` | 3 221 880 kB |
| `RssAnon` | 2 516 200 kB (**99.4% of RSS**) |
| `RssFile` | 14 164 kB |
| `RssShmem` | 0 |
| largest single mapping | `[anon:mimalloc]` **2 450.7 MB** |
| next mapping | the `simple` binary, 13.5 MB |
| `Pss` | 2 516 752 kB — essentially equal to Rss |
| `Shared_Clean` | 14 160 kB |
| `Swap` | 0 |

**The answer to "where does it go" is: one mimalloc heap arena.** It is not the
page cache, not mapped source, not the binary. Nothing is shared with sibling
workers (`Pss ~= Rss`, 14 MB shared = the binary's text), so the cost of N
workers is exactly N x per-worker heap.

Growth is monotone and never returns: across the sampling window every observed
worker climbed **2.40 -> 2.74 GB** and none fell. Combined with
`VmPeak 3.37 GB > VmHWM 2.41 GB`, this is retention plus allocator arena growth,
not transient spikes.

What fills that arena, from source (`Explore` pass over the driver):

| structure | site | lifetime |
|---|---|---|
| SoA retained source text (`source_contents_owner` et al) — full text of **every** closure file | `driver_source_pipeline_loading.spl:318-347` | process exit |
| `ctx.sources` boxed `SourceFile` records duplicating the same fields | `driver_source_pipeline_parsing.spl:421-433` | process exit (second inventory) |
| frozen `ModuleSurfacesByName`, `module_surfaces_promote(...)` | `parsing.spl:447-486` | process-immortal by design |
| flat AST arena / token interner — `ast_reset()` reallocates, never shrinks | `parsing.spl:226-258` | process exit |
| `parsed_entry_modules: [ParsedEntryModuleBox]` | `parsing.spl:552, 619` | whole entry-closure loop |
| per-file parse garbage | `rt_transient_array_scope_begin/end`, `parsing.spl:270-330` | correctly scoped — **not** a problem |

**But the dominant term is none of those.** It is the compiler self-closure the
child loads *before doing any work*: parse-shard children are spawned as the
full CLI, ~665 modules / ~3.3 GB, for ~80 files of parsing. See §4.

## 2. Is `--threads 8` optimal?

**The thread count is derived from CPU count alone. Nothing anywhere derives it
from memory.**

- Parsed in exactly one place, `src/app/cli/native_build_main.spl:314-328`
  (`--threads|--jobs|-j`); default is `0` (= no sharding) unless a caller asks.
- The real chooser is `scripts/bootstrap/bootstrap-from-scratch.sh:897-945`:
  `host_cpus=$(getconf _NPROCESSORS_ONLN)`, then `jobs=$((host_cpus / 2))`
  (`2` on CI; `host_cpus` for `clean-release`; self-host capped to `2` in the
  `incremental` profile).
- On this 32-core host that default is **16**, i.e. ~16 x 2.5 GB = **40 GB for a
  single run** before the driver's own footprint.

Model, using the measured per-worker constant and the fact that sharding is a
flock'd dynamic work queue (`driver_source_pipeline_parsing.spl:133-196`), so
work splits cleanly but each worker pays a large fixed startup:

- wall ~= `fixed_startup + parse_work / N` ; memory ~= `N x per_worker`.
- `fixed_startup` is the closure load, currently ~16-26 s and ~3.3 GB. It does
  **not** shrink with N, so beyond the point where `parse_work/N` is comparable
  to `fixed_startup`, extra workers buy almost no wall time and cost 2.5 GB each.
- Once `N x per_worker` exceeds free memory the machine pages/OOMs and wall time
  goes to infinity — observed today as two runs dying with `rc=255`.

**Recommendation:** make the default `min(host_cpus/2, floor(MemAvailable_GB /
per_worker_GB x 0.6))`, and with the §4 fix in place (`per_worker ~= 1.5 GB`)
that lands at **4-6 on a shared box, 8 on an idle one** — not 16. Evidence: at
1.5 GB/worker, 8 workers = 12 GB, which fits alongside two sibling lanes on this
box; at the current 2.5-3.3 GB/worker, 8 workers = 20-26 GB and three lanes
cannot coexist in 125 GB. This is a proposal; see §5.

## 3. Duplication across workers — ranked

| # | finding | evidence | fix sketch | risk |
|---|---|---|---|---|
| 1 | **Parse-shard children load the whole compiler closure** (~665 modules / 3.3 GB) to parse ~80 files. A slim parse-lane entry exists (383 modules / 0.88 GB) and is unwired. | `native_build_main.spl:377` spawns `native_build_worker.spl`; `parse_shard_main.spl:1-10` and `driver_parse_shard_entry.spl:6-11` | one-line restore — **done in this change**, see the bug record | none; parse sharding is a cache warm-up that cannot change output |
| 2 | **Zero page sharing between workers.** Children are `spawn`+`exec`, so the identical closure is re-materialised N times as private dirty heap (`Pss ~= Rss`, 14 MB shared). | measured, §1 | fork the orchestrator *after* the closure is built so COW shares it; or the sibling lane's frozen-surface persistence | high — changes process model; needs the interpreter to be fork-safe. Propose only. |
| 3 | **Full entry-closure source text loaded and retained in every worker**, regardless of which shard owns which file. | `compile_targets.spl:968-978, 1001-1011`; `loading.spl:318-347` | let a shard load only text for modules it may own, or mmap instead of retaining `text` | medium — the queue lets a shard claim any module, so ownership is dynamic; needs lazy load, not a static filter |
| 4 | **The streaming surface path has no shard-ownership check** — every worker parses and surfaces every source; the shard exit is only after the loop. | `parsing.spl:333-420` vs the check at `:584`, exit at `:486` | apply `_driver_parse_shard_owns` inside the streaming loop | medium — must not break surface completeness for the real build |
| 5 | **`ctx.sources` duplicates the SoA source inventory** — two live copies of every file's text. | `parsing.spl:421-433` vs `loading.spl:318-347` | have `SourceFile` borrow indices into the SoA owner rather than copy | medium |
| 6 | **O(n^2) COW array growth in the load loop**: `all_sources = all_sources.push(s)` where each element carries full file text. | `loading.spl:143, 252, 266, 296, 304`; same shape `parsing.spl:427` | mutate through the single owner (`.claude/rules/code-style.md`) | low — mechanical |
| 7 | **HIR shard children also spawn the full worker** and rebuild closure + frozen surfaces each. | `native_build_main.spl:445`; `doc/08_tracking/bug/hir_shard_children_reparse_closure_2026-08-22.md` | owned by the sibling cache lane — coordinate, do not implement | — |
| 8 | **mimalloc never returns the arena** (2 450 MB single anon mapping; RSS monotone). | measured, §1 | evaluate `MIMALLOC_PURGE_DELAY` / `mi_option_purge_decommits` for worker children only | low, but measure before adopting — purge costs CPU |

Items 2 and 7 overlap the sibling frozen-surface cache lane; this lane did not
touch them.

## 4. Memory-pressure backoff

**There is none.** The only reader of `/proc/meminfo` in the build path is
`scripts/check/check-heavy-work-preflight.shs:100-141`, a one-shot admission
gate: it fails if `MemAvailable < MIN_MEM_GIB`, if swap used > 2 GiB, or if
`load_1m > cpu_count/MAX_CPU_FRACTION`. It never lowers the thread count — it
exits non-zero. `SIMPLE_BOOTSTRAP_LOW_MEMORY=1` and `--low-memory` select a
static code path, not a pressure response.
`bootstrap-progress-watch.shs:105-217` samples RSS for logging only.

**Smallest safe mechanism, proposed (not implemented — it changes build
behaviour):** clamp the *chosen* thread count at spawn time, in
`native_build_main.spl` next to `native_build_shard_threads`, to

```
cap = max(1, floor(MemAvailable_GB * 0.6 / worker_budget_GB))
threads = min(requested, cap)
```

with `worker_budget_GB` read from the same constant
`scripts/check/check-parse-shard-rss-budget.shs` already pins (`BUDGET_KB`,
1.65 GB), and the clamp logged (`[parse-shard] threads=N (requested M, capped by
MemAvailable=X GB)`). Properties that make it safe: it only ever *reduces*
concurrency, sharding is a cache warm-up so output is unchanged at any N, it
reads one file once at spawn, and `SIMPLE_SHARD_MEM_CLAMP=0` disables it. It is
deliberately not a mid-run feedback loop — killing or suspending live shards
would re-open the orphaned-claim class fixed by `6cedd51faec`.

## 5. Actions taken by this lane

- Fixed: restored the slim parse-shard entry (one line) —
  `doc/08_tracking/bug/parse_shard_slim_entry_reverted_6cedd51faec_2026-08-23.md`.
- Filed the above; proposed §4 and duplication items 2-6 without implementing.
