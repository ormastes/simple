# HIR shard worker RSS grows ~110 KB per import resolution before any HIR lowering (2026-11-05)

Status: root cause measured on the admitted Stage 2 binary; source fix landed in
`src/compiler/80.driver/driver_entry_closure_core.spl`; native before/after slope
awaits the next bootstrap re-run (the Stage 2 worker is compiled in, so a
worktree edit cannot be A/B'd on the admitted binary).

## Symptom (bootstrap-opus-2, run 2 after #6736)

Stage 2 admitted (`stage2-admitted/simple` sha256 `90cffcd700f6af5c...`), then
the mandatory `compiler_cli_build` row (`native-build
src/app/cli/_CliMain/main_and_help.spl --backend=cranelift --low-memory
--threads 2`) was killed at the 54525952 KiB tree cap with two HIR shard
workers at ~25 GiB each. The log's last HIR rows read `done=208` / `done=190`
of 3006, which the first reading took as ">24 GiB per worker at ~7% of HIR,
growing linearly with modules lowered". That premise is wrong: the memory was
already there before the first module was lowered.

Logs: `build/bootstrap-opus-2/logs/aarch64-unknown-linux-gnu/stage2-compiler-tests.log`,
`.../stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`.

## Reproduction (same binary, this host)

`native-build` of the same entry from a git worktree with the bootstrap's
frontend policy (`SIMPLE_SHARD_MEM_CLAMP=1 SIMPLE_HIR_SHARD_WORKER_KB=9000000
SIMPLE_PARSE_SHARD_WORKER_KB=25165824 SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=54525952`)
under `systemd-run --user --scope -p MemoryMax=56G`, sampling `/proc/PID/status`
every 2 s:

| t (s) | worker 0 VmRSS | worker 1 VmRSS | phase |
|---|---|---|---|
| 49 | 5.2 GiB | 5.2 GiB | pre-surface (closure walks) |
| 104 | 12.0 GiB | 12.0 GiB | pre-surface |
| 190 | 21.7 GiB | 20.9 GiB | pre-surface |
| 231 | 25.5 GiB | 25.6 GiB | pre-surface, no `surfaces-ready` yet |

Zero HIR modules lowered at 25 GiB. The two workers are
`stage2-admitted/simple run src/app/cli/native_build_worker.spl ... --hir-shard=i/2`
(internal route in `src/app/cli/bootstrap_main.spl`; the worker code is
compiled in -- a worktree `src/compiler` edit does not reach it, verified
with a gated probe that never printed; its symbol table carries the Rust
runtime's transient-scope implementation
(`simple_runtime::value::collections::TransientHeapScope`, mangled
`rt_transient_array_scope_end` closures), so that is the memory model the
numbers below describe).

## Attribution (gdb on one standalone worker, same argv/env, no symbols needed)

Breakpoints on `rt_transient_array_scope_end` calling `rt_heap_live_bytes`,
`rt_heap_aux_live_bytes`, `rt_heap_registry_count`, `rt_process_rss_kib`
(scripts: `/tmp/claude-1000/-home-yoon-dev-simple/bbdffaa3-fe88-4fba-9d31-a0ed4e45c64b/scratchpad/workerenv/gdbscript{,2,3,4,5,6,7}`,
logs `gdb{1..7}.log` beside them; the worker was re-run standalone from its
captured `/proc/PID/{environ,cmdline,cwd}` under `MemoryMax=30G`):

| scope ends | heap live | aux live | registry objects | RSS |
|---|---|---|---|---|
| 1 000 | 66 MB | 48 MB | 1.0 M | 212 MB |
| 12 000 | 618 MB | 309 MB | 10.8 M | 1.6 GB |
| 16 000 | 2.10 GB | 1.21 GB | 40.8 M | 6.5 GB |
| 24 000 | 3.45 GB | 1.66 GB | 67 M | 11.1 GB |
| 58 150 | 9.42 GB | 3.30 GB | 179 M | 25.9 GB |

The first `phase2:surface:file:parse-start` line appears only after scope end
58 150. Every sampled scope-end backtrace is
`_driver_file_natively_owns_v1` <- `driver_closure_native_owner_v1` <-
`driver_library_mode_native_owner_v1`, i.e. one scope per import resolution.
From scope end ~13 000 on (the worker's `worker_admitted_edges_selected_v1`
walk, `driver_worker_surface_closure_v1.spl`), one `_driver_file_natively_owns_v1`
call per scope end and, per 200 resolutions (gdb6, heap-live deltas between
events):

| segment | bytes retained per 200 resolutions |
|---|---|
| `driver_library_mode_resolve_v1` entry -> owner-check entry (the resolver) | 13-22 MB |
| owner-check entry -> its scope begin (cached source scan) | 1-3 MB |
| inside the owner-check scope | 0.4-0.6 MB |
| scope end -> next resolver entry (`_driver_resolve_entry_import`, keys, deps) | 8-16 MB |

So ~110-190 KB per resolution is retained OUTSIDE the only scope on the path.
Per 500 resolutions the resolver performs (gdb7) ~13 500 `rt_dir_list`,
~50 000 `_driver_resolver_path_exists_v1`, ~14 000
`_driver_try_numbered_entry_import_rel_checked_v1`, ~6 000
`_driver_canonical_source_path`: ~27 directory listings and hundreds of path
strings per resolution, all allocated with no transient scope active and
therefore process-immortal in the no-GC runtime. Promotions in this phase: 2
(gdb4), so nothing is being retained on purpose; it is unscoped scratch.

The same pattern runs in the CLI entry closure (`_native_build_entry_closure`)
and phase-1 `load_sources` (scope ends < 12 000 above: ~45 KB per resolution),
which is the parent's 1.2 GB peak; the worker repeats the whole closure's
edge resolution a second time for its admitted-edge graph, and that walk is
the 25 GB.

Not causal, recorded for completeness: 30x `[hir-shard] cache store refused
(codec, not I/O)` (`enum wire enum allocation failed`, same class as the
2026-11-04 record), and a one-off +1 GB heap / +3.7 GB RSS step at the
phase-1 -> phase-2 transition (not attributed here).

## Fix

`src/compiler/80.driver/driver_entry_closure_core.spl`: the two resolver
entry points now own a transient scope per call and promote only their
answer:

- `_driver_resolve_source_root_entry_import_from_v1` (source-root resolver
  shared by the CLI walk, phase-1 and the worker graph) wraps the former body
  (`_driver_resolve_source_root_entry_import_scratch_v1`);
- `_driver_resolve_entry_import_untimed` (checkout resolver, called by
  `driver_closure_native_owner_v1` after the owner check and by the
  `Missing` fallback) wraps `_driver_resolve_entry_import_scratch_v1`.

`_driver_resolver_scratch_begin_v1` returns false (no own scope) when the
caller already holds an active or paused scope, mirroring
`_driver_file_natively_owns_v1`; `_driver_resolver_scratch_end_v1` pauses,
promotes the answer (`SourceRootResolutionV1` or text; scalar/`Missing`
answers are a no-op success in both runtimes) and ends the scope, failing
closed with a panic exactly like the existing owner-check scope. Neither
resolver writes a process memo (audited: the only module-level containers on
the path are `_g_entry_scan_*`, written by `_driver_cached_entry_source_scan`,
which is reached only from the owner check BEFORE its scope, and the
preprocessor memos, which the resolver never calls; the hot probes
`_driver_resolver_path_exists_v1` (epoch dict read + `rt_file_exists`),
`dir_exists`, `_driver_numbered_child_dir`, `_driver_try_entry_import_rel`,
`_driver_resolve_numbered_compiler_import` and `_driver_canonical_source_path`
write no module-level container).

Expected effect: a worker's pre-surface retained set becomes the real
retained data (source inventory, scan cache, surfaces) instead of 25 GB of
resolver scratch, so `compiler_cli_build` stays under the 54525952 KiB cap
into HIR. The per-source candidate scans in
`worker_admitted_edges_selected_v1` (`driver_closure_import_specs_from_source_v1`,
`worker_surface_import_ids_v1`, bounded by source count, ~0.5 GB for 4439
sources) are deliberately left unscoped: `_pp_preprocess_conditionals`
writes `pp_strip_memo_log` in target/cfg modes and a scope there would free
memo values.

## Verification

- Seed (`/home/yoon/dev/cargo-rel100/simple-ref`, interpreted driver): the
  interpreter's heap counters are flat across this phase (seed1/seed2
  `[MEMPROBE]` lines), so it cannot show the native slope; it exercises the
  scope protocol (begin/pause/promote/end) on the same code and must build
  the same closure without a `resolver scratch ... failed` panic.
- Resolver micro-benchmark (seed, interpreted, same Rust runtime; script
  `/tmp/claude-1000/-home-yoon-dev-simple/bbdffaa3-fe88-4fba-9d31-a0ed4e45c64b/scratchpad/t/resolver_bench.spl`:
  12 spellings x 100 rounds through both resolver entry points, run from the
  fixed worktree and from a clean worktree at base `d349866ad0b`):

  | | resolutions | found | elapsed | heap delta | RSS delta |
  |---|---|---|---|---|---|
  | base | 2400 | 2400 | 4557 ms | +127 745 B | +888 KiB |
  | fixed | 2400 | 2400 | 4599 ms | +145 B | -1 772 KiB |

  Same answers, time within noise (+0.9%), and 2400 begin/pause/promote/end
  cycles over both answer types without a scope panic. The interpreter lane
  retains only ~53 B per resolution to begin with (its values are freed), so
  the 110 KB/resolution native slope cannot be reproduced here; this is the
  protocol/parity check, not the slope A/B.
- Driver specs (seed `simple-ref test`, worktree vs a clean worktree at the
  same base `d349866ad0b`): `entry_closure_core_shared_state_spec` 3/3,
  `driver_hir_worker_surface_v1_spec` 3/3, `lazy_named_import_closure_spec`
  9/9 pass; `native_entry_closure_gate_source_spec` 3/6,
  `native_build_closure_owner_hygiene_spec` 1/2 and
  `worker_surface_differential_spec` 10/11 fail the SAME tests on the clean
  base (identical failing-line sets), so they are pre-existing, not caused
  here.
- Native slope before vs after: the next sanctioned bootstrap run, i.e. the
  run-2 invocation from `build/bootstrap-run2.log` (from
  `/home/yoon/dev/simple-bootstrap`, once this commit is on the tree):
  `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
  --stop-after-stage2 --backend=cranelift --output=build/bootstrap-opus-3
  --produce-stage3-receipt=verify-landed-compiler-fix
  --produce-managed-receipt=self-host-convergence-check`.
  Comparators in `stage2-compiler-tests/.../compiler_cli_build.log`: worker
  RSS at `[hir-shard] surfaces-ready` (before: >25 GiB per worker, killed at
  the 54525952 KiB cap; expected after: low single-digit GiB) and `elapsed_ms`
  on the `phase=parse ... current=complete` row (before: 403 450 ms). Native
  timing before/after is UNMEASURED here; the scope end only calls
  `malloc_trim` when >= 16 MB was freed, so a ~110 KB scope never trims, and
  what disappears is 58k x 27 immortal directory listings, so the expectation
  is not-slower.
- Trap hit while measuring: editing a worktree after a `native-build` has
  taken its SCV snapshot fails the next build with
  `SCV-E-ADMISSION: snapshot-index-drift:<file>`; `rm -rf build/scv` in that
  worktree clears it.
