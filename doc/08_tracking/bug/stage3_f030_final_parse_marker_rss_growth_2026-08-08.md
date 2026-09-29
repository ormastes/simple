# Stage 3 self-host at f030 stalls after its final parser-progress marker while RSS grows

- **ID:** `stage3_f030_final_parse_marker_rss_growth_2026-08-08`
- **Status:** OPEN — one bounded, externally terminated observation; root cause not yet attributed
- **Severity:** high — blocks the canonical pure-Simple Stage 3/Stage 4 chain and therefore safe runtime redeploy
- **Scope:** pure-Simple compiler bootstrap only; no deployed-runtime, Rust-seed, QEMU, or Vulkan conclusion is implied

## Observation

In an isolated worktree at source revision
`f03097413fff7cc46a8c8a47bdabf8e2cd72d7bf`, the canonical full bootstrap was
started with an isolated output directory and without deployment:

```sh
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_BOOTSTRAP_PROGRESS_LOG=build/production-runtime-admission-f030/bootstrap-progress.log \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --full-cli --no-mcp --jobs=min \
  --output=build/production-runtime-admission-f030 --progress
```

Stage 2 completed successfully (796 compiled, 0 cached, 0 failed; 1057.9 s).
Stage 3 then used the admitted Stage 2 compiler to build
`src/app/cli/bootstrap_main.spl` with `--threads 1`, `--mode dynload`, and
`core-c-bootstrap`.

The retained progress log records real CPU work (~100% of one core) and the
following Stage 3 sequence:

| elapsed | progress record | tree RSS |
|---|---|---:|
| 30:08 | `parse files=64/555 tasks_done=1/6` | 914,396 KiB |
| 30:38 | `parse files=192/555 tasks_done=1/6` | 1,875,280 KiB |
| 31:09 | `parse files=320/555 tasks_done=1/6` | 2,890,892 KiB |
| 31:39 | `parse files=320/555 tasks_done=1/6` | 3,762,800 KiB |
| 32:09 | `parse files=555/555 tasks_done=1/6` | 4,931,036 KiB |
| 32:39 | same final marker | 5,926,928 KiB |
| 33:09 | same final marker | 6,957,812 KiB |

The operator delivered `SIGTERM` to preserve host headroom. The wrapper
recorded `exit-143`; it did not produce a Stage 3 candidate or deployment.
The next 30-second sample was expected after the process had crossed roughly
8 GiB, but was intentionally not taken after termination.

## Exact attribution boundary

`src/compiler/driver/driver_source_pipeline_parsing.spl` emits the final
`parse files=555/555` record immediately after the final
`parse_full_frontend()` result is stored. It emits no further progress marker
while it materializes alias module names and returns its `CompileContext`.
The next driver-owned marker (`parse modules=... tasks_done=2/6`) occurs only
after `parse_all_impl()` returns; Phase 3 HIR begins immediately afterward.

Therefore the final progress value is a **stale parser marker**, not proof
that `src/std/nogc_sync_mut/io/sffi_common.spl` was executing. This observation
is bounded to either:

1. post-final-file work in the native-entry-closure branch of
   `driver_source_pipeline_parsing.spl`, or
2. the subsequent Phase 3 HIR/typecheck transition.

No profile or stack was captured while the process was live. Retained build
artifacts provide progress and receipt data only, so a retrospective stack
attribution would be fabricated.

## Known non-matches

- This is not the fixed re-export chase
  (`stage3_selfhost_nonterminating_reexport_chase_2026-08-06`): that failure
  was frozen at `tasks_done=2/6`, was localized to nine nested
  `find_reexport_source` frames, and was fixed in `548f2d3b1f6`.
- It is not the fixed `functions=-1` post-HIR runaway
  (`stage4_post_hir_corrupt_module_runaway_2026-08-02`).
- It resembles the open self-host parse/AST retention family
  (`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20`) in monotonic
  RSS growth, but this Stage 3 run did not enable `SIMPLE_COMPILER_PHASE_PROFILE`
  or a heap-registry sink. It must not be assigned that root cause yet.

## Owner and required next evidence

The canonical owner is the pure-Simple compiler driver/frontend boundary:
`src/compiler/driver/driver_source_pipeline_parsing.spl`, with HIR transition
instrumentation in `src/compiler/driver/driver_orchestration.spl` and the
existing profile helper in `src/compiler/driver/driver_log_helpers.spl`.

Before any bounded replay, rebuild Stage 2 from source carrying the existing
profile hooks, then run the recorded Stage 3 command with:

```sh
SIMPLE_COMPILER_PHASE_PROFILE=1 \
SIMPLE_COMPILER_PHASE_PROFILE_FILE=<isolated-output>/stage3-phase-profile.log
```

Acceptance for that one replay is a durable marker sequence that distinguishes
`phase2:parse:file:done`, `phase2:parse:done`, and
`phase3:hir_typecheck:start`, each with `heap_registry` count. Only then may a
fix be scoped. Preserve the retained Stage 2 cache and do not retry this build
until that diagnostic plan is approved.

## Retained evidence

- output root: `build/production-runtime-admission-f030/`
- progress: `build/production-runtime-admission-f030/bootstrap-progress.log`
- structured progress: `build/production-runtime-admission-f030/bootstrap-build-progress.events`
- Stage 3 log: `build/production-runtime-admission-f030/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- admitted Stage 2: `build/production-runtime-admission-f030/stage2/x86_64-unknown-linux-gnu/simple`
