# Stage-2 dynload build peaks ~10GB and OOMs; --low-memory eviction does not cover the dominant retention

Date: 2026-09-17
Host: Windows 11, Git Bash, x86_64-pc-windows-gnu, cranelift backend, jobs=1

## Symptom

The Stage-2 pure-Simple native build (`bootstrap_main.spl`, dynload mode,
~890 cache entries) grows linearly and peaks around 10 GB in a single
`simple` process, then aborts with a Rust allocation failure:

```
memory allocation of 119808 bytes failed
```

First observed as an 8.1 GB peak (attempt 16, completed); later attempts OOM'd
when the box carried parallel load (15.7 GB total RAM).

## What was ruled out

- `--low-memory` was NOT reaching the driver at all on this path: the Stage-2
  invocations in bootstrap-from-scratch.sh never passed the flag, and
  bootstrap_main.spl parsed it away without setting options.low_memory
  (only the _CliCompile route and the interpreter path set it). Fixed in
  this branch (flag threaded to all three dynload invocations;
  bootstrap_main sets options.low_memory from args).
- With options.low_memory = true the AST eviction (ctx.evict_ast after phase
  3 / analyze) runs, but the peak is UNCHANGED (~10 GB, still OOMs).
- The dynload module cache is small (203 MB, 3 entries in the stage2
  cache dir), so retention is not loaded dynlib bodies.

## Measurements

- simple process WS during Stage-2 build, low_memory=false: 2.9 -> 8.8 GB
  over ~5 min (attempt 22), then OOM.
- simple process WS, low_memory=true (flag verified reaching the driver via
  the wired bootstrap_main): 6.7 -> 10.0 GB (attempt 23), then OOM.
- Growth is ~linear at ~1.3 GB per 45 s with jobs=1, i.e. per-module
  compiler state retained across modules (MIR/decl arenas, C-ABI lowering
  state, or the AOT per-module accumulators are the likely owners;
  driver_orchestration/driver_aot_native_output eviction only covers AST
  and, under --output-format both, MIR).

## Why CI does not see it

Linux CI lanes have more headroom and typically run with cache-warm stages;
the growth still happens but stays under the limit.

## Suggested direction

1. Profile the per-module retention (heap snapshot with
   --diagnostics, or SIMProfiler counters per phase) and extend eviction to
   the dominant owner (MIR decl arenas per module after native emission is
   the first candidate: aot pipeline already has driver_mir_eviction_enabled
   gates at driver_aot_native_output.spl:1700/1837/2101).
2. Interim mitigation for low-memory hosts: compile stage-2 in module
   shards with a fresh process per shard (the check worker already chunks
   this way; CHECK_CHUNK_SIZE=32 in check_entry.spl) and link incrementally.
3. The bootstrap's own low-memory mode should additionally skip the
   frontend cache or bound it when SIMPLE_BOOTSTRAP_LOW_MEMORY=1.

Related: the 7 GB budget goal for this host requires fix (1) or (2); the
current peak is ~10 GB regardless of the flag.
