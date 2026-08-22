# Parse-shard work queue: a dead shard's claims are orphaned (2026-08-22)

**Status:** FIXED
**Area:** `src/app/cli/native_build_main.spl` (orchestrator), `src/app/cli/parse_shard_queue.spl` (new, std-only)
**Introduced by:** 9b23f334a9b (flock'd claim-marker work queue for parse shards)

## Symptom (run11, stage1, 2026-08-21)

`stage1_build.log`:

```
[parse-shard] done shard=1/8 parses=94 claimed=94
error: TIMEOUT: killed by kill_simple_monitor (cpu=101% ... age=901s>=900s: ... --parse-shard=6/8)
[parse-shard] 7/8 shard(s) completed split=queue
```

Shard 6/8 never printed a `done` receipt. The orchestrator counted the
non-zero `rt_process_wait` result and dropped it -- nothing named the shard,
its pid, or why it died. Its ~48 claim markers stayed in the queue with no
front-end cache entry behind them; every other shard had already skipped
those modules as "someone else's", so nothing ever parsed them into the
cache, and every downstream consumer (8 HIR shards, then the real build)
re-parsed the same ~48 modules.

## Root cause

1. Death: `scripts/resource/kill_simple_monitor.shs` CPU guard (age >= 900s,
   `SIMPLE_TIMEOUT_SECONDS`), not OOM. The orchestrator has no way to tell:
   `run_parse_shards` did `if code == 0: done += 1` and nothing else.
2. Orphaning: the claim protocol is claim-then-parse with no release path.
   The design comment ("a module that is never claimed ... is simply parsed
   by the real build") covered the *unclaimed* case only; a claimed-but-dead
   module was invisible.

## Fix

- `spawn_parse_shards` prints every child's outcome:
  `[parse-shard] shard=i/n pid=P exit=0` or
  `... FAILED exit=N | SIGNAL/abnormal | TIMEOUT` (labels from
  `parse_shard_exit_label`, mapping rt_process_wait's 0 / >0 / -1 / -2).
- After all shards exit, `parse_shard_release_claims(queue_dir, dead_specs)`
  deletes every marker whose content is a dead shard's spec, and the dead
  indices are spawned once more. All surviving claims (and their cache
  entries) are untouched, so the retry claims exactly the orphans. One
  round only; a second death degrades to the real build parsing the rest,
  exactly as before.

## Tests

`test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl` -- simulated
death-after-claim (markers owned by `6/8`), multi-dead, no-dead/unpublished
queue, exit labels, and a source pin that the orchestrator logs each exit
and reclaims before printing `shard(s) completed`. Fails pre-fix (4/5),
passes post-fix (5/5).

Pre-existing, unrelated: `parse_shard_execution_mode_spec.spl` example
"decides shard ownership before emitting the in-flight parse receipt" is RED
on origin/main (receipt precedes the ownership test in
`driver_source_pipeline_parsing.spl`); not touched here.

## Operational note: the killer and the orchestrator env

Shard 6/8 was killed by `scripts/resource/kill_simple_monitor.shs` (CPU
guard: `cpu=101% ... age=901s>=900s`), not by the kernel OOM killer. A parse
shard legitimately runs at 100% CPU for many minutes, so stage orchestrators
(bootstrap stage drivers, fp*/run* lanes) MUST export
`SIMPLE_TIMEOUT_SECONDS=0` (disables the CPU guard) before spawning
`native-build --threads N`; otherwise the monitor will keep killing the
slowest shard at 900s and the reclaim round only halves the damage.
