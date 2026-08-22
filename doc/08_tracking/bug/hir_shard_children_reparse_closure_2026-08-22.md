# HIR shard children re-parse the whole closure from source (front-end cache scope split by entrypoint script)

- **Date:** 2026-08-22
- **Status:** FIXED (this record's commit)
- **Area:** native-build `--threads` HIR sharding (`01303371443`, `7a014363f8b`), parse-shard slim entry (`5409b246adc`)
- **Severity:** perf, blocks bootstrap stage1 (8x the whole parse phase, ~1 h per child, serialized before any lowering)

## Symptom

run10 (tree `1ffdfb58baf`, seed `e5f12c93…`, `--threads 8`, `SIMPLE_CACHE_SCOPE=run10`,
non-streaming path, 687-module closure): the 8 parse shards finished at +1771 s
(`[parse-shard] 8/8 completed`, 687 `.fpc` entries on disk). The 8
`native_build_worker.spl --hir-shard=i/8` children then spent >54 min in
`parse ~286/687 step 1/6` with real parse costs (`module_surface_export_index.spl`
dt=17-19 s in EVERY child vs 22 s in the parse shard that parsed it; restores
elsewhere cost ~0.5-1 s) and no `[hir-shard]` receipt. Per-entry `.fpc` mtimes
showed the cache being REWRITTEN from 07:15 on, i.e. every child missed and
re-stored.

## Root cause

`native_build_compiler_executable_hash()` (`src/compiler/80.driver/driver_build/incremental.spl`)
hashes `rt_cli_get_args()[0]`. Under `simple run <script>` that is the **script**,
not the compiler binary. The "exe=" field of the producer identity — and with it
`SIMPLE_FRONTEND_CACHE_SCOPE` (the header every `.fpc`/`.hir` entry is checked
against) — therefore depends on which entrypoint script a process was started with:

| process | script | exe= |
|---|---|---|
| parse-shard child | `src/app/cli/parse_shard_main.spl` | `cd27ff61…` = sha256(parse_shard_main.spl) |
| HIR-shard child, real worker | `src/app/cli/native_build_worker.spl` | `f5dd94de…` = sha256(native_build_worker.spl) |

All 378 entries the parse shards wrote carry the first scope; every lookup from an
HIR child is a foreign-scope MISS, so each child re-parses the closure (and
re-stores it under the second scope, which is why the later real build still
hit). Introduced by `5409b246adc`, which moved parse shards onto a slim
entrypoint; before that every process ran `native_build_worker.spl` and the
identities happened to agree (that is why `native_build_hir_sharding_spec`'s
`hits=3` held — it pinned the HIR cache, not the front-end cache the children read).

## Fix

`native_build_compiler_executable_hash()` hashes `SIMPLE_BINARY` (the resolved
compiler path the orchestrator publishes before spawning any shard or worker)
when set and present, falling back to `args[0]`. Every process of one build — and
every build run by the same compiler — now shares one identity; entries carry
`exe=<sha256 of the compiler>` as the name always claimed.

## Evidence (fixture `native_build_cache`, `--threads 2`, seed `e5f12c93…`)

Pre-fix: HIR child 1 `[frontend-cache] hits=0 misses=3 parses=3`; child 0 hit only
because child 1 had already rewritten the entries. Post-fix: both HIR children and
the real build `hits=3 misses=0 parses=0`; all `.fpc` headers `exe=e5f12c93`;
output binary byte-identical to the pre-fix build. `check-hir-codec-roundtrip.shs`
PASS (3 modules, binary identical); `native_build_hir_sharding_spec` 2/2 passed
with the new pin `count_of("[frontend-cache] hits=3 misses=0 parses=0") == 3`
(pre-fix value 1).

Time-to-first-lowering on the stage1 closure: before = never within 54 min
(child still at parse 286/687); after = closure (~20 s) + 687 restores at
~0.5-1 s (measured restore cost of the same entries in run10's children) ≈ 6-12
min per child instead of ~1 h each, and lowering starts as soon as the restores
finish. Not re-measured at full scale here (run10 was left running untouched).

## Not done (follow-up)

Each HIR child still rebuilds the source closure and the frozen surfaces itself
(~16-26 s at +0 in run10) before it can claim modules; `01303371443` intended
that ("run through parse (all hits) and the surface freeze"), and the driver
does not persist frozen surfaces, so loading them from a cache is a separate
feature, not part of this fix.
