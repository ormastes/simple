# Every worker child re-loads the compiler + stdlib as an interpreted program, uncached (2026-08-23)

Status: **open** — root cause measured and located; the fix is architectural and
is deliberately NOT attempted in this lane.

Lane: L4 of `doc/03_plan/compiler/bootstrap/phase1_build_duration_plan_2026-08-23.md`.

## The brief's framing, and why it is wrong

The L4 brief says: "each [worker] pays ~12s to read 82 `src/lib/**` sources.
8 shards x 9 passes ~= 864s per attempt", and proposes reusing the existing
frontend `.fpc` cache (which reports `hits=688 misses=0`) to cover them.

**Reusing the `.fpc` cache cannot fix this, because the `src/lib` reads in
question never reach that cache — they are not the same population of work.**
There are two distinct populations, and the brief conflates them:

1. **The compiled closure** — the modules the build is actually compiling.
   These DO go through the parse cache:
   `driver_source_pipeline_parsing.spl:566` (`for source in unique_entry_sources`)
   -> `parse_full_frontend` (`:587`)
   -> `frontend.spl:145` `frontend_parse_or_restore`
   -> `frontend.spl:108` key / `:119` store.

2. **The interpreter's own module loader** — loading `src/compiler/**` and
   `src/lib/**` so that the pure-Simple driver can *itself run*, interpreted,
   under the seed. **This path never calls `frontend_parse_cache_*` at all.**

Population 2 is the cost. It is the compiler loading *itself*, not the compiler
parsing the program under compilation.

## Evidence

Measured 2026-08-23 on `/mnt/fast/wt/buildwarm-1` (box at load ~72/32 cores, so
treat wall times as an envelope, not a floor).

A whole small-closure `native-build` of a 2-line hello world produced **exactly
one** `.fpc` entry:

```
build/bootstrap/native_cache/<lane>/frontend/cb1c6e2d….a92.fpc
sha256sum /mnt/fast/bw/hello.spl -> cb1c6e2d….a92
```

The one cached module is the entry file itself — correct behaviour, since
`hello.spl` imports nothing, so `unique_entry_sources` has one element. There is
**no predicate anywhere excluding `src/lib`**; the stdlib simply is not in the
compiled closure of that build.

Meanwhile, `strace -f -qq -e trace=openat` over the same build (partial capture,
~21k `openat` lines, so these are **lower bounds**):

| population | count |
|---|---|
| successful `src/lib/**.spl` opens | 343 (121 distinct) |
| max repeat of a single file | 28x (`src/lib/io_runtime.spl`); then 20, 10, 9, 8, 8 |
| parent pid 2322603, `src/lib` opens | 68 |
| child pid 2328754, `src/lib` opens | 275 |
| child pid 2328754, `src/compiler/*.spl` opens | 1326 (1133 distinct) |

The child repays the entire load — and the `src/compiler` load (1326 opens) is
an order of magnitude larger than the `src/lib` load the brief focused on.

## Why the parse cache cannot be pointed at it as-is

`frontend_parse_cache_enabled()`
(`src/compiler/10.frontend/frontend_parse_cache.spl:72`) requires
`SIMPLE_FRONTEND_CACHE_SCOPE`, which is published only by
`_driver_publish_frontend_cache_scope()`
(`src/compiler/80.driver/driver_source_pipeline_parsing.spl:198-202`, called from
`:345` and `:563`) — that is, *inside the driver*, long after the interpreter has
already finished loading the compiler and stdlib in order to run that driver.
The load is complete before the cache is even switched on. This is an ordering
property of "the compiler is an interpreted Simple program", not a missing
`if` that can be flipped.

`driver_source_pipeline_loading.spl` contains **zero** references to
`frontend_parse_cache`; the parse cache is a phase-2 concept there. Its stdlib
enumeration is at `:126-127`
(`parse_bootstrap_default_root("./src/lib/nogc_sync_mut" / "./src/lib/common")`,
bootstrap-defaults branch only) and the bulk load at `:289`
(`["src/app","src/lib","src/compiler","src/runtime"]`), which is suppressed
under `--entry-closure` by `:286`.

## What a real fix requires

Caching the *interpreter's* module loading — not the frontend parse cache:

- an `.smf`-backed (or otherwise serialised) image of the compiler+stdlib module
  graph that each child maps rather than re-parses; or
- a pre-forked worker parent that loads the compiler+stdlib once and forks per
  shard, so children inherit the loaded graph.

Both change the process model. The fork option in particular changes the RSS
picture, which is owned by the per-worker-memory lane — coordinate before
starting. Neither is a minimal semantics-preserving edit, which is why this lane
recorded it rather than attempting it.

**Constraint any fix must preserve:** `.claude/rules/commands.md` documents that
a `src/lib/**` edit needs NO build step — the stdlib is read as SOURCE every
run. So the image/fork must be keyed by source content (the way `.fpc` entries
are keyed by `sha256` of the file bytes) and must fail closed to a real load on
any mismatch. Cache it transparently; do not introduce a build step.

## Separate, real defect found alongside: the scope memo can latch OFF

**Filed in its own right as
`doc/08_tracking/bug/frontend_parse_cache_scope_memo_latches_off_2026-08-23.md`,
which is the authoritative record** (it also carries the method note on
refutations naming their tree). Summarised here only for context.

Distinct from the above, and actionable on its own.

`frontend_parse_cache_scope()`
(`src/compiler/10.frontend/frontend_parse_cache.spl:62-70`) **latches
`_fe_cache_scope_memo` on its first call** and never re-reads the environment.
`_driver_publish_frontend_cache_scope()`
(`src/compiler/80.driver/driver_source_pipeline_parsing.spl:198-202`) runs only
in phase 2 (from `:345` and `:563`).

So on any path where a parse happens in phase 1, the memo latches `""` and the
parse cache is **off for the entire process**, silently. That is exactly the
**bootstrap-defaults** stage build: `driver_source_pipeline_loading.spl:60`
parses all of `src/compiler` plus `src/lib/{nogc_sync_mut,common}`
(`:126-127`) before any publish.

This did NOT fire in the measurement above, because `:126-127` sit inside
`if input_len <= 0:` (`:118`) and an `--entry` build has `input_len > 0` — which
is why that run still reported `parses=1` with the cache on. It is latent on the
`--entry`-less stage path.

`src/compiler/80.driver/driver_hir_cache.spl:70` calls the same memoized getter
and can latch it early too — but the HIR cache is owned by another lane, so that
half must be coordinated with them, not fixed here.

Likely minimal fix: do not memoize a NEGATIVE result (treat `""` as "not yet
published, ask again") — or publish the scope before any phase-1 parse. Either
is small; neither was attempted in this lane because it needs its own
failing-pre-fix reproduce on a bootstrap-defaults build, which is a full stage
build this lane was constrained not to run.

## Not to be confused with L3

L3 (frontend parse cache destroyed by the build-context cache clear) is a
separate, now-fixed defect — see
`scripts/bootstrap/native-cache-clear.shs` and
`scripts/check/check-frontend-cache-survives-context-change.shs`. Fixing L3 does
nothing for the cost described here, and vice versa.
