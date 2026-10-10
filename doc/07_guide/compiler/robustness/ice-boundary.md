# Per-module ICE boundary (native-build)

Robustness item 10a. Code: `src/compiler/80.driver/driver_ice_boundary.spl`.
Spec: `test/01_unit/compiler/driver/ice_boundary_acceptance_spec.spl`.

## What it prevents

A failure inside one module's MIR lowering or object codegen used to end the
build at that module, and a worker that crashed was reported only as an exit
status. One bad module hid every other problem and cost a full re-run each.

Now each module is compiled inside a boundary. A failed module is recorded and
named, the remaining modules are still compiled, and the build still fails.

## Two tiers: caught and attributed

Simple has no try/catch, and a panic or an access violation ends the process.
So the boundary is honest about two different strengths.

| Tier | Failure kinds | What happens |
|---|---|---|
| caught | Anything the compiler returns as a value: `Err` from `lower_module_transient_scoped`, a missing HIR module, `Err` from per-module codegen (`_compile_selected_module`) | Recorded in-process. The phase continues with the next module. |
| attributed | The process dies inside a module: panic, nil dereference trap, access violation, SIGSEGV/SIGBUS, abort, kill | Not catchable. The parent reads the breadcrumbs, names the module, and re-launches the worker past it. |

A fatal `MirError` diagnostic (for example `undefined variable`) is a user
error, not an ICE. It was already collected for all modules and is unchanged.

## How it reports

Files live in `build/ice/` (override: `SIMPLE_ICE_DIR`).

- `ice_breadcrumbs.log` — `start` is appended before each module and `done`
  after it. A module with `start` and no `done` is where a worker died.
  Deleted at the end of a clean build.
- `ice_receipt.tsv` — written only when a module failed. One tab-separated
  row per failed module, then one summary row:

```
ice_v1	kind=caught	phase=mir_lower	module=mod.bad	path=src/mod/bad.spl	function=	backend=	message=...
ice_summary_v1	failed=1	caught=1	attributed=0	modules=mod.bad
```

`\t`, `\n` and `\` inside a value are escaped. `phase` is `mir_lower` or
`codegen`; `backend` is set for `codegen`.

Console and error list:

```
ICE[mir_lower] module mod.bad (caught): MIR lowering transient scope failed for mod.bad: ...
1 module(s) failed with ICE: mod.bad (mir_lower, caught) (receipt: build/ice/ice_receipt.tsv)
```

The build result is `CodegenError` carrying that summary, so the exit code is
non-zero.

When a worker dies, the parent (`run_native_build_worker`) prints

```
error: ICE: native-build worker died (exit status -1073741819) inside codegen of module mod.bad (src/mod/bad.spl); re-launching past it, 2 retries left.
```

and re-launches the worker with the module on `SIMPLE_ICE_SKIP_MODULES`. The
re-launched worker records the module as `attributed`, compiles the rest, and
exits non-zero. A timeout is never re-launched.

## Switches

| Setting | Effect |
|---|---|
| default | Record and continue. Up to 2 worker re-launches after a crash. |
| `SIMPLE_ICE_BOUNDARY=fail-fast`, `SIMPLE_COMPILE_FAIL_FAST=1`, or `--fail-fast` | Record the first failed module, then stop. No re-launch. |
| `SIMPLE_ICE_BOUNDARY=off` | No boundary work at all: no breadcrumbs, no receipt, no re-launch. First failure ends the phase as before. |
| `SIMPLE_ICE_CRASH_RETRIES=<n>` | Re-launch budget after a worker death (0 = attribute only). |
| `SIMPLE_ICE_DIR=<dir>` | Where breadcrumbs and receipt go. Set it per lane when two builds share a working directory. |

The MIR phase also stops once the existing poison budget (200 modules) is spent.

## Adding a case

Test-only fault knobs, read by `ice_boundary_module_start`:

- `SIMPLE_ICE_INJECT_MODULE=<module>[,<phase>:<module>...]` — that module fails.
- `SIMPLE_ICE_INJECT_KIND=abort` — the process exits 134 inside the module
  instead of returning a failure (a real death, for the attributed tier).

To put a new per-module step behind the boundary, call
`ice_boundary_module_start(module, path, phase, backend)` before it. A
non-empty result means "do not compile, record this message". On failure call
`ice_boundary_fail(...)` and add its return value to the error list; on
success call `ice_boundary_module_done(module, phase)`. Every orderly path must
end in one of the two, or the module will be reported as a dead worker.

## Known limits

- `function` is always empty: lowering does not expose the function in flight.
- After a module fails in MIR lowering the build stops at the end of that
  phase. Sibling modules are lowered to MIR but not code-generated.
- After a caught MIR failure the shared lowering state is reused, so a later
  failure in the same run can be a consequence of the first.
- Each re-launch after a crash repeats the whole worker run (object cache
  helps codegen, MIR lowering is redone).
- Not covered: the LLVM group-pair codegen path, HIR shards (they have their
  own crash ledger), and the grouped native child.
- The in-process single-file route has no parent. After a crash there, the
  module is the open `start` line in `ice_breadcrumbs.log`.
- Two concurrent builds in one working directory share `build/ice/` unless
  `SIMPLE_ICE_DIR` is set.
