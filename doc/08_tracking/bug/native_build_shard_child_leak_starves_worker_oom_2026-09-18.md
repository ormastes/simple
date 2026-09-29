# Parse/HIR shard children leak after "FAILED TIMEOUT" and starve the native-build worker (OOM)

Date: 2026-09-18
Lane: release v1.0.0-beta line (kimi-20260915-beta2)
Severity: release-blocking (windows-x86_64 + linux-x86_64 legs)
Status: mitigated in v1.0.0-beta.10 (kill dead shards + heartbeat + SIMPLE_PARSE_SHARDING=0 on CI legs); root cause of the shard child dying open.

## Symptom

Release `v1.0.0-beta.9` windows-x86_64 leg:

```
[parse-shard] shard=0/1 pid=8620 FAILED TIMEOUT (orchestrator wait expired)
[hir-shard] 0/2 shard(s) completed split=static     <- 33 ms later: HIR shard spawns failed
...worker warnings for ~31 s...
memory allocation of 65520 bytes failed
native-build worker was KILLED by signal 1073740663
```

## Evidence

- beta.7, beta.8, beta.9 ALL show `[parse-shard] shard=0/1 ... FAILED TIMEOUT` on
  darwin-arm64, darwin-x86_64 and windows-x86_64. The cache-warming shard child has
  NEVER completed on a GitHub runner (6-12 min of total silence, then the wait
  returns "TIMEOUT" — a -2 label).
- `rt_process_wait` keeps a timed-out child **tracked but alive**; nothing killed it.
  The leaked shard keeps its multi-GiB seed-interpreter heap resident while the HIR
  phase and the real worker run.
- beta.9: by the HIR phase the runner could no longer spawn children (0/2 in 33 ms);
  the worker then died on the first unlucky allocation ~31 s in.
- beta.7 is the control: same leaked shard, but the (then-smaller) closure still fit
  in the 16 GB runner, so the worker compiled everything and only failed later at
  SCV inventory publication (a different bug, since fixed).
- Local repro (Windows, isolated cache): the seed interpreter running the
  native-build orchestrator reached **31 GB working set in 12 minutes** while merely
  loading its graph — the seed-interpreted driver is far heavier than the runner
  economics allow when several copies coexist (orchestrator + shard + worker).

## Root cause (worker OOM)

1. Parse shard child is spawned with the full 6 h wait but dies/diverges silently on
   the runner (exact exit path unknown — it prints nothing, not even its graph-load
   warnings; a `-2` label means either the wait deadline or a child exit code that
   reads as -2 on Windows).
2. `spawn_parse_shards` / `run_hir_shards` never kill a failed child (same gap the
   HIR phase had).
3. Worker starts with GBs already committed by orchestrator + leaked shard →
   allocation failure on a 16 GB runner.

## Fix (v1.0.0-beta.10)

- `spawn_parse_shards` / `run_hir_shards`: `process_kill(pid)` any child whose wait
  did not return 0; log the kill.
- `parse_shard_main.spl`: heartbeat print at `main()` entry so future logs can
  distinguish "child never started" from "child started then died".
- release.yml + build-binaries.yml: `SIMPLE_PARSE_SHARDING=0` on the native-build
  legs (linux-x86_64, macOS, windows-x86_64, Stage 2 linux/mingw). Sharding is a
  pure cache warm-up; with it off the worker parses in-process (proven to fit by
  beta.7) and no shard heap can leak. HIR sharding keys off the same env and
  disables itself.

## Open

- WHY the shard child dies silently on every GitHub runner while the same command
  prints its graph-load warnings locally within ~1 min. Candidates: runner memory
  pressure during the seed interpreter's eager front-end graph load; a Windows
  exit-code mapping that renders a specific death as -2. The beta.10 heartbeat line
  `[parse-shard] child alive ...` will settle "started vs never started".
- The orchestrator's own unbounded graph-load growth (31 GB local) is a seed
  interpreter perf/mem bug by itself; the pure-Simple self-hosted binary does not
  exhibit it. Tracked here until split out.
