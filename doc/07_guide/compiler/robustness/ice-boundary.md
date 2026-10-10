# Per-module ICE boundary (native-build)

Robustness item 10a. Code: `src/compiler/80.driver/driver_ice_boundary.spl`.
Spec: `test/01_unit/compiler/driver/ice_boundary_acceptance_spec.spl`.

## What it prevents

A failure inside one module's MIR lowering or object codegen used to end the
build at that module, and a worker that crashed was reported only as an exit
status. One bad module hid every other problem and cost a full re-run each.

Now each module is compiled inside a boundary. A failed module is recorded and
named, the remaining modules are compiled where that is safe, and the build
still fails.

## What is on by default, and what is opt-in

| Behaviour | Default |
|---|---|
| Codegen bracket: per-module `Err` recorded with backend, siblings continue | on |
| Missing HIR module in MIR lowering: recorded, siblings continue | on |
| Receipt and "N module(s) failed with ICE" summary | on |
| Parent names the module a dead worker was inside (message + receipt row) | on |
| Parent re-launches the worker past that module | **opt-in** (`SIMPLE_ICE_CRASH_RETRIES=<n>`) |

## Three kinds of failure

Simple has no try/catch, and a panic or an access violation ends the process.

| Kind | Examples | What happens |
|---|---|---|
| caught, continues | `Err` from per-module codegen (`_compile_selected_module`); a missing HIR module | Recorded in-process. The phase goes on with the next module. |
| caught, stops | `Err` from `lower_module_transient_scoped` | Recorded, then the phase returns at once. That `Err` is only returned after the lowering arena was aborted, so lowering another module on the shared instance would be use-after-reclaim. |
| attributed | The process dies inside a module: panic, nil-dereference trap, access violation, SIGSEGV/SIGBUS, abort, kill | Not catchable. The parent reads the breadcrumbs and names the module. |

A fatal `MirError` diagnostic (for example `undefined variable`) is a user
error, not an ICE. It was already collected for all modules and is unchanged.

## Run directory and ownership

The boundary works only inside a run directory, named by `SIMPLE_ICE_DIR`.

- The native-build parent (`run_native_build_worker`) is the only owner. It
  creates `build/ice/<pid>_<hash of output path>/`, exports it to its worker,
  empties it before each worker launch and removes it after a clean build.
- A worker only appends, and only to files named after its own pid. It never
  resets or deletes.
- At claim time the owner also prunes old run directories under the same root:
  only those with an `ice_owner` marker older than a day whose owner pid is not
  running, at most 64 entries examined per claim. Directories without a marker
  are never touched.
- A process that was handed no directory does no boundary work: JIT, plain
  `compile`, and the in-process single-file native-build route behave exactly
  as before.

Two builds from one working directory therefore have different directories and
cannot read, attribute or delete each other's files. `SIMPLE_ICE_ROOT` moves
the `build/ice` root.

## How it reports

- `ice_breadcrumbs.<pid>.log` — one file per writing process. `start` is
  appended before each module and `done` after it. A `start` with no `done`
  after the worker has exited is a module it died in.
- `ice_receipt.<pid>.part` — the rows one process recorded. Several processes
  in one build (for example grouped children) never share an append target.
- `ice_receipt.tsv` — written by the owner after the workers have exited, only
  when a module failed: every part's rows, then one summary row. A directory
  with a receipt is kept as evidence until a later claim prunes it.
- `ice_owner` — owner pid and creation time, used for pruning.

An orderly failure that is not an ICE (for example release's `E-MONO-038`
check after a successful lowering) closes the module's breadcrumb first, so it
is never reported as a dead worker.

```
ice_v1	kind=caught	phase=mir_lower	module=mod.bad	path=src/mod/bad.spl	function=	backend=	message=...
ice_summary_v1	failed=1	caught=1	attributed=0	modules=mod.bad
```

`\t`, `\n` and `\\` inside a value are escaped. `phase` is `mir_lower` or
`codegen`; `backend` is set for `codegen`.

Console and error list:

```
ICE[mir_lower] module mod.bad (caught): MIR lowering missing HIR module for mod.bad (src/mod/bad.spl)
1 module(s) failed with ICE: mod.bad (mir_lower, caught) (receipt: build/ice/4711_n82/ice_receipt.tsv)
```

The build result is `CodegenError` carrying that summary, so the exit code is
non-zero.

When a worker dies, the parent prints, with no re-launch:

```
error: ICE[codegen] module mod.bad (attributed): worker died inside this module (worker exit status -1073741819)
```

If several modules were in flight the death belongs to one of them and every
row says so: `one of 2 modules in flight: mod.p, mod.q`.

## Re-launch past a crash (opt-in)

With `SIMPLE_ICE_CRASH_RETRIES=<n>` the parent re-launches the worker with the
dead module on `SIMPLE_ICE_SKIP_MODULES`, up to `n` times. Each re-launch is a
full worker run. The parent fails the build whenever a re-launch happened,
whatever the last worker reports.

Never re-launched: SIGKILL or SIGTERM (for example an out-of-memory reaper),
exit status -1 (wait failure or wrapper death), and a timeout. None of them
says the module in flight is at fault. The module is still named.

## Switches

| Setting | Effect |
|---|---|
| default | Record and continue as in the table above. No re-launch. |
| `SIMPLE_ICE_BOUNDARY=fail-fast`, `SIMPLE_COMPILE_FAIL_FAST=1`, or `--fail-fast` | Record the first failed module, then stop. Never re-launches. |
| `SIMPLE_ICE_BOUNDARY=off` | No boundary work: no directory, no breadcrumbs, no receipt, no message prefix, no environment changes. Release behaviour. |
| `SIMPLE_ICE_CRASH_RETRIES=<n>` | Re-launch budget after a worker crash. Default 0. |
| `SIMPLE_ICE_ROOT=<dir>` | Root for run directories. Default `build/ice`. |

The MIR phase also stops once the existing poison budget (200 modules, 1 under
fail-fast) is spent.

## Adding a case

Test-only fault knobs, read by `ice_boundary_module_start` (a run directory
must be set):

- `SIMPLE_ICE_INJECT_MODULE=<module>[,<phase>:<module>...]` — that module fails.
- `SIMPLE_ICE_INJECT_KIND=arena` — fails as a lowering failure that already
  aborted its arena (the stop-at-once path).
- `SIMPLE_ICE_INJECT_KIND=abort` — the process exits 134 inside the module
  (a real death, for the attributed tier).

To put a new per-module step behind the boundary, call
`ice_boundary_module_start(module, path, phase, backend)` before it. A
non-empty result means "do not compile, record this message". On failure call
`ice_boundary_fail(...)` and add its return value to the error list; on
success call `ice_boundary_module_done(module, phase)`. Every orderly path must
end in one of the two, or the module will be reported as a dead worker. Do not
keep going after a failure that leaves shared compiler state half-reclaimed.

## Known limits

- `function` is always empty: lowering does not expose the function in flight.
- After a module fails in MIR lowering the build stops at the end of that
  phase. Sibling modules are lowered to MIR but not code-generated.
- Not bracketed: the LLVM group-pair codegen path
  (`_driver_group_pair_execute_v1`), HIR shards (they have their own crash
  ledger), and the grouped native child. A crash there is not named, and a
  module on the skip list that takes the group-pair path on a re-launch is not
  recorded by the worker; the parent still fails that build.
- The in-process single-file route has no parent, so the boundary is inert
  there.
- A kill cannot be told from a crash on Windows by exit status alone
  (`TerminateProcess` chooses the status), so an opted-in re-launch can follow
  an external kill there.
