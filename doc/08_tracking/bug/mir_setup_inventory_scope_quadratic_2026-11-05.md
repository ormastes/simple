# MIR setup inventory scopes are quadratic in the closure: 545-569 s prescan starves the MIR shard workers (2026-11-05)

Status: root cause measured on the admitted Stage 2 binary; source fix in
`src/compiler/80.driver/driver_pipeline_lowering.spl` (one transient scope per
setup phase instead of one per module, plus the promotion share window);
native after-timing awaits the next bootstrap re-run (the driver is compiled
into the Stage 2 binary, so a worktree edit cannot be A/B'd on it).

## Symptom (bootstrap-opus-3, run 3, release/1.0.0 a6174dbdbe9, aarch64)

`compiler_cli_build` (full CLI closure, 3006 modules) finished HIR at
~965 s, then both MIR shard workers sat in MIR setup until their 1800 s
`--timeout` budget ran out: `[mir-shard] owner=0/2 status=BLOCKED exit=-2
claimed=0`, `owner=1/2 ... claimed=0`, `blocked=worker could not be reaped`,
`MIR shard aggregate failure`. Log:
`build/bootstrap-opus-3/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`.

**Reading the progress rows correctly.** `log_build_progress` prints
`current=<phase>` when a phase STARTS, and `dt_ms` is the delta since the
previous row. The two rows

```
elapsed_ms=1526300 dt_ms=545085 current=mir_setup:enum_inventory
elapsed_ms=1535034 dt_ms=569141 current=mir_setup:enum_inventory
```

therefore measure the phase BEFORE enum_inventory: 1526300 - 981215 and
1535034 - 965893 are the two workers' `mir_setup:struct_prescan`. The first
framing ("~569 s in enum_inventory") was off by one phase. No
`composite_inventory` row ever appeared in the log, and both workers ended
with `claimed=0`; the log carries no row after the enum_inventory start, so
whether they were still in the enum or composite phase when the 1800 s
budget expired is inferred from the budget (worker stdout can be dropped by
the relay chain, so this is not observed).

## Root cause

#5709 (`5781b6e3f10`, "compiler: bound MIR setup transient scopes") wrapped
every module of the three setup loops -- struct prescan
(`prescan_module_struct_names`), enum inventory
(`register_module_enum_inventory_v1`) and composite inventory
(`register_module_composite_inventory_v1`) -- in its own
`transient_array_scope_begin_v1()` / `_driver_mir_inventory_scope_end`.

`_driver_mir_inventory_scope_end` (`driver_pipeline_lowering.spl:106` before
this fix) calls `MirLowering.promote_transient_owner()`
(`src/compiler/50.mir/_MirLowering/transient_owner.spl`), which promotes
**280** field roots one by one through `rt_transient_heap_promote`
(`src/runtime/runtime_native.c:3351`). That walk does not stop at already
persistent nodes: `rt_core_transient_classify` (`runtime_native.c:3161`)
answers 1 for every registered array/dict/enum/closure, promoted or not, so
each root promotion traverses the whole reachable registry graph -- which is
the inventory itself and grows with every module registered. Unlike
`lower_module_transient_scoped` (`module_lowering.spl:2529`), the driver
helper opened no `rt_transient_heap_promote_share_begin` window, so the 280
roots re-walked the shared graph independently.

Cost per module = O(280 x accumulated graph); per phase = O(modules^2);
three phases per process; and every MIR shard worker repeats the whole setup
before its first claim (the log carries one complete `mir_setup:*` row set per
worker), so two workers paid it twice in parallel. The seed's Rust
`rt_transient_heap_promote` (`compiler_rust/runtime/src/value/collections.rs:3081`)
walks the same way (only a share window skips committed children), so the
interpreter path is quadratic too.

The inventory loops themselves are linear and were never the problem:
`register_module_enum_inventory_v1` is one `enums.values()` walk per module
and `register_enum_variants` dedups by name.

## Measurements (before)

Admitted Stage 2 binary
`build/bootstrap-opus-3/stage2/aarch64-unknown-linux-gnu/simple`
(sha256 `6bb69e9220400c15e7dc7f25dd3b82d23e7944101dd2ddf76b335b21a382d1ed`),
`native-build --entry-closure --entry src/app/test_runner_new/main.spl
--threads 1`, 319 modules, `SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_PHASE_RSS=1`,
idle host (load < 2):

| phase | wall | rss_kib at done |
|---|---|---|
| struct_prescan | 2122 ms | 1852640 |
| enum_inventory | 2227 ms | 1852756 |
| composite_inventory | 2378 ms | 1852768 |

Prescan `visited=` checkpoints every 64 modules, one process: +210 ms,
+253 ms, +427 ms, +454 ms, +641 ms (last 63) -- the per-block cost grows
linearly with modules already registered, i.e. the phase is quadratic. The
enum inventory, which registers a handful of names per module, costs the
same as the prescan: the cost is the scope end, not the registration.

Same binary inside the bootstrap (loaded host, two workers):
`test_runner_build` (319 modules) 5202 / 6329 ms prescan, 4841 / 5973 ms
enum inventory; `compiler_cli_build` (3006 modules) 545085 / 569141 ms
prescan. (3006/319)^2 x 5.5 s ~ 490 s, consistent with quadratic scaling;
the enum and composite phases would have added a comparable amount each,
past the 1800 s worker budget.

Interpreter A/B was attempted and did not complete inside the lane's time
box -- see "After" below.

## Fix

`src/compiler/80.driver/driver_pipeline_lowering.spl`:

- One transient scope per setup PHASE: `transient_array_scope_begin_v1()`
  before each loop, `driver_mir_inventory_scope_end_v1` once after it (both
  prescan branches, enum, composite). 3 scope ends per process instead of
  3 x modules. Everything the phases allocate that must survive is promoted
  exactly as before (the registries are retained either way); only the
  per-module temporaries (`.values()`/`.keys()` arrays) now live until the
  phase end instead of the module end -- a few hundred bytes per module.
- `driver_mir_inventory_scope_end_v1` wraps `promote_transient_owner()` in
  `transient_heap_promote_share_begin_v1` / `_end_v1`, the same window
  `lower_module_transient_scoped` uses, so the 280 roots share one walk:
  O(roots x graph) -> O(graph) for the one promotion the phase pays.
- `visited=` checkpoints every 64 modules in the enum and composite loops,
  matching the prescan.
- `driver_mir_inventory_digest_v1`: sorted `registry|key|value` rows over
  every NAME-keyed registry the three phases write (`struct_field_order`,
  `struct_field_has_default`, `class_type_names`, `enum_variant_index`,
  `enum_registration_current`, `enum_variant_payload_kind`), printed as
  `aot:mir_setup:inventory_digest rows=<n> sha256=<hex>` when a phase trace is
  on; `SIMPLE_MIR_INVENTORY_DUMP=<path>` writes the rows for a line diff.

Identical-output check:
`test/01_unit/compiler/80.driver/mir_setup_inventory_phase_scope_spec.spl`
registers a three-module fixture (enums, a same-named struct in two modules,
a class) under the old per-module cadence and the new per-phase cadence on
two lowerings, asserts the scopes really opened (9 vs 3 scope ends on the
seed runtime) and requires byte-identical digests. The driver's
`aot:mir_setup:inventory_digest` line on a real closure is the native
before/after check for the next bootstrap (same `rows=`/`sha256=` expected).

Related specs re-run on the seed after the change: `module_enum_inventory`
5/5, `module_composite_inventory` 6/6, `bootstrap_enum_inventory` 3/3 (all
OK); `test/01_unit/compiler/mir/class_prescan_collision_spec.spl` fails 1/1
("keeps same-named classes and structs distinct across modules") both on
this change and on the pristine `origin/release/1.0.0` worktree, and imports
no driver module -- pre-existing, not caused here.

Not changed: `promote_transient_owner` itself (the simple-mir-scope lane owns
the transient-scope / E-MIR-TYPE-Transport fix in `transient_owner.spl`),
and the runtime walk. Making the walk stop at persistent nodes would be the
asymptotic fix, but without a write barrier a persistent registry dict can
hold a scope-allocated child, so stopping early would free live rows.

## After -- NOT YET MEASURED (honest status)

- Native: the driver is compiled into the Stage 2 binary, so the admitted
  binary cannot run the fixed code. The after-number is the
  `mir_setup:struct_prescan` -> `enum_inventory` -> `composite_inventory`
  `dt_ms` rows of the next bootstrap's `compiler_cli_build.log` (expected:
  each phase a single graph walk, i.e. seconds to tens of seconds for 3006
  modules, not 545-569 s for the prescan alone).
- Interpreter: `/home/yoon/dev/cargo-rel100/simple-ref native-build
  --source src/compositions/kernel_llvm_cranelift --source src/compiler
  --source src/app --source src/lib --source src/os --entry-closure --entry
  src/app/test_runner_new/main.spl --threads 1` with `SIMPLE_BOOTSTRAP=1
  SIMPLE_PHASE_RSS=1` under `systemd-run --scope -p MemoryMax=30G`, once on
  a pristine `origin/release/1.0.0` worktree and once on the fixed worktree.
  Neither run printed a `[build] phase=` row within the lane's time box
  (pristine run: >20 min at 99 % CPU, RSS flat at ~1.86 GB, log still at
  the startup banner), so no interpreter before/after pair exists. A
  hello-world closure under `--source build/tmp_hello` died earlier still
  (`parse-shard closure snapshot roots mismatch`, before MIR). The
  CLAUDE.md before/after requirement is therefore met only on the BEFORE
  side (admitted Stage 2, identity above); the after side is owed by the
  next bootstrap run.

What the change can and cannot cost in memory: there is no per-scope
allocation ceiling in `runtime_native.c` (the raw-block table only grows;
HIR per-file scopes already reach millions of raw blocks, `runtime_native.c:2252`),
so holding one phase's temporaries in one arena is within the runtime's
normal envelope. `RT_CORE_TRANSIENT_MAX_NODES` (4M, `runtime_native.c:3068`)
caps a single promotion PLAN -- the walk over the whole reachable graph --
and that walk is the same size under either cadence, so the cap is a
pre-existing limit for the 3006-module closure, not a new one.

## Worker timeout and the "could not be reaped" block (separate bug)

- `exit=-2` is `rt_process_wait`'s "still running" poll result
  (`src/runtime/runtime_process.c:3500`); the parent surfaces it when
  `time_now_monotonic_ms() - started_ms >= timeout_ms`
  (`src/app/cli/native_build_main.spl:1072`), `timeout_ms` = `--timeout`
  (1800 s) counted from the worker's spawn. Workers do not wait on a shared
  inventory; each rebuilds the whole MIR setup itself, which is why both
  died with `claimed=0`.
- After the deadline the parent sends SIGTERM (`rt_process_kill`,
  `runtime_process.c:97`) and waits 5000 ms; a worker still alive after that
  is "could not be reaped" and blocks the queue. Workers are spawned with
  SIGTERM reset to default (`posix_spawnattr_setsigdefault`,
  `runtime_process.c:1567`), so a worker that survives 5 s of SIGTERM is
  either stopped under the cgroup memory pressure or has a child holding the
  pgroup. There is no SIGKILL escalation; `rt_process_kill_tree`
  (`runtime_process_tree.c:411`) exists but is not used on this path.
  Recorded here, not fixed in this change (the reap path is the shard
  coordinator's, outside this lane's scope); the fix is a SIGKILL + re-wait
  escalation after the 5 s SIGTERM grace.

## `JoinPoint` re-registration warning (verdict: harmless, keep)

Three distinct structs share the bare name: `compiler/10.frontend/core/aop.spl:162`
(`kind, kind_function_name, kind_signature, kind_location, kind_error_type,
block_id, instruction_index, context`), `compiler/35.semantics/join_point_model.spl:115`
(`kind, source_symbol, target_symbol, logical_join_point_id`) and
`compiler/85.mdsoc/weaving/join_point.spl:7`. The prescan keeps the FIRST
bare-name row and records the collision in
`struct_field_order_conflict_warned` (`module_lowering.spl:1843`). Field
resolution (`function_lowering.spl:2040-2070`) consults the per-module
`field_map` and the module-qualified layout key first; the bare row is a last
resort, and for a name in the conflict set it fails closed with
`error_fatal("field ... on ambiguous struct/class name ...")` instead of
using the keep-first layout. So the warning is a canary, not a miscompile;
it prints once per worker process (hence twice per name in the log). The
same holds for the other 20-odd names in the log (`TextSpan`, `ByteSpan`,
`FileStat`, `Task`, ...). Renaming the three `JoinPoint`s would silence it;
not done here.
