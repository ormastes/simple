# Native build: memory blowup right after a MIR shard's last object (2026-11-21)

**Status:** OPEN. Step narrowed, root cause NOT proven, no source fix landed.
**Lane:** `native-build` of the bootstrap CLI, two-pass shard lane
(`SIMPLE_FILE_WORKERS=0`), 2 MIR/codegen shard children of ~800 modules,
`--cache-dir` set, serial codegen. Compiler: admitted Stage 2 built from
`0d8a3269bec`; build source `b142aca5572`.

## Measurement

30-second RSS trail of the run (tree / largest process):

| time | tree | largest | event |
|---|---|---|---|
| 23:02-23:30 | 41.1 -> 42.3 GB | 19.7 -> 20.5 GB | codegen, flat |
| 23:30:26 | | | shard A writes its last object |
| 23:32:11 | 42.7 GB | 20.8 GB | still flat |
| 23:32:41 | 43.8 GB | 21.9 GB | growth starts |
| 23:32:55 | | | shard B writes its last object |
| 23:33:11 | 46.9 GB | 24.5 GB | |
| 23:33:41 | 50.4 GB | 28.1 GB | ~7 GB/min |
| ~23:34 | | | 52 GB cgroup OOM kill |

No log line between `[NATIVE] codegen: ... serial lane` and death. A
single-process run died the same way (1538 objects by 22:07:11, killed
22:13:26).

## What the evidence rules out

- **Not `build_cache.save()` / the reverse-reference receipt** (the first
  suspect, `driver_build/incremental.spl` `incremental_reverse_reference_generation_v1`).
  A shard child runs `compile_to_native` with `native_staged_codegen.flushing`
  set (`driver_aot_pipeline.spl:826`), so it takes the `save_entries()` arm
  (`driver_aot_native_output.spl:2980`) and never builds the receipt. Where the
  receipt is built in this lane it holds 15 rows (measured on two builds): every
  family is `registry-not-published`.
- **Not the build-cache save itself.** `save_entries()` after the loop took 7 ms
  on a 31-module fixture (strace), and the per-module saves during codegen are
  transient-scoped.
- **Not the linker, not codegen.** The shard ledger of the failed run
  (`<cache>/hir/mir-queue-*/`) holds 1601 `.claim`, 0 `.object`, 0 `.terminal`:
  the child died before the first `native_mir_shard_publish_pass_v1`
  (`driver_aot_pipeline.spl:867`), i.e. inside `compile_to_native` after
  `builder.build` returned.

## What was measured on the old binary (fixtures, 4 GB cap)

Synthetic closures built with the admitted Stage 2 binary, `strace -f -k`:

| fixture | post-codegen time | scratch per module | retained |
|---|---|---|---|
| 321 modules x 2 tiny fns | < 1 s total | ~0 | +17 MB |
| 31 modules x 30 fns (600 lines) | 0.4 s/module | ~75 MiB alloc + free | ~0 |
| 31 modules x 20 fns + 180 statics | 0.55 s/module | not measured | +80 MB once |

In the post-process loop (`driver_aot_native_output.spl:2857-2974`) each module
costs time and scratch proportional to its MIR, not to the module count. The
scratch is ~5x the module's MIR (75 MiB against ~15 MiB) and is released by
`rt_transient_array_scope_end` (+ `malloc_trim`) once per iteration. The only
transient scope opened in that loop is `driver_capture_initializer_object_v1`
(`cache/initializer_object_capture_v1.spl:14`, called at `:2923`), which passes
`ctx.mir_modules[name]` (a `struct MirModule`) to
`mir_initializer_plan_finalize_v1`, which walks `module.functions.values()`.
Attribution to that call is by elimination: the binary's symbol table did not
resolve the frames.

## Estimate against the failure

Held MIR is ~20 GB per 800-module child, ~25 MB per module, so ~125 MB of
scratch per module. At the measured 0.16-0.4 s per module that is 19-47 GB/min
of allocation. The observed +7 GB/min is 15-40% of it, and A's 2 flat minutes
are 0.16 s x 746 modules if the loop had finished, or its first third if not.

**Not explained:** the fixtures reclaim the scratch every iteration; the failed
run evidently did not. The blowup was not reproduced under a 4 GB cap, so
whether the retained memory is this scratch, and why scope end stops returning
it at 20 GB of live heap, is unverified. The 2 flat minutes are also
unexplained if the scratch leaks from the first iteration.

## Knobs present in `0d8a3269bec` (none verified against the blowup)

- `SIMPLE_MIR_SHARD_WORKER_KB=<kib>` (`app/cli/file_worker_pool_refusal.spl:214`,
  `app/cli/native_build_main.spl:1513`): per-worker MIR budget. Lower it to get
  more, smaller shard children; each then holds less MIR and runs a shorter
  post-process loop. Also changes shard concurrency and the admission maths.
- `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=<n>` (`driver_build/native_staged_codegen.spl:30`,
  read at `driver_aot_pipeline.spl:134`): single-process lane only; lowers,
  emits and evicts `n` modules at a time. Refused (with a `[staged-codegen]
  refused` line) on ineligible lanes; a shard child always uses batch 0.
- `SIMPLE_KEEP_MIR=1` (`driver_aot_native_output.spl:2271`) only disables MIR
  eviction: more memory, not less. Omitting `--cache-dir` does not skip the
  loop; the cache moves to the machine cache root.

## Next step

Run one shard child of the real closure under `strace -f -k -e trace=brk,mmap`
(or a heap profile) with enough headroom to cross the growth onset, and read
the allocating frames. `SIMPLE_MIR_FORK_BATCH` (added after `0d8a3269bec`,
`3d3011bbce2`) bounds the held MIR per child and may hide the defect rather
than fix it.
