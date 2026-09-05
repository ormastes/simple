# test_runner JIT fallback: `Cannot infer field type: struct 'FunctionOutline' field 'type_params'` drops the whole runner to the interpreter

- **Date:** 2026-08-17
- **Status:** FIXED 2026-08-17 (`cd26d63985ba`) — see "Root cause" below
- **Severity:** High (fleet-wide test throughput)
- **Component:** compiler HIR lowering / JIT; trigger file `src/app/test_runner_new/main.spl`

## Exact error

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'FunctionOutline' field 'type_params' [in src/app/test_runner_new/main.spl]: whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Cannot infer field type: struct 'FunctionOutline' field 'type_params' [in src/app/test_runner_new/main.spl]
```

## Trigger

Every `bin/simple test <spec>` invocation. HIR lowering cannot infer the type
of `FunctionOutline.type_params`, so the entire `src/app/test_runner_new/main.spl`
module — the test runner itself — executes under the interpreter, not the JIT.

## Measured cost

- Solo run of `test/03_system/database/server/db_durability_spec.spl` under
  `timeout 300` never reaches a verdict (still in setup at 300s); with
  `timeout 590` it completes: 22/22 pass, but setup alone exceeds 300s.
- 2026-08-17 system-suite sweep: 5 of 8 suite logs (app, browser_engine,
  compiler, core, database) ended `Terminated` immediately after the runner
  banner — killed by the harness timeout while still in interpreter-speed setup,
  with zero tests executed.
- The `03_system_coverage` suite that did finish reported
  `setup: 248340ms` (~4 min) for a 3s test payload.

Evidence logs:
`scratchpad/agentlogs/03_system_{acceptance,app,browser_engine,check,compiler,core,coverage,database}.log`
(session e29ebf0f, 2026-08-17).

## Why this is the single highest-leverage fix

Because the fallback is per-module and the module is the runner entry point,
every spec in the fleet pays the ~100-1000x interpreter penalty during
discovery/setup. Fixing the one un-inferable field type (or annotating
`FunctionOutline.type_params` explicitly) restores JIT execution for the whole
test fleet and would bring suite setup from minutes back toward seconds.

## Root cause (2026-08-17)

Not a type-inference gap: **plain wrong source**. The error is raised by
`src/compiler_rust/compiler/src/hir/lower/expr/collections.rs:415`, which
validates a struct/class **literal**'s named arguments against the declared
field list when the declaration is in the same file. It is NOT a field-access
inference failure, which is why `SIMPLE_DEBUG_FIELD_FAIL=1` printed nothing.

Five `DebugConfig(...)` literals passed `args:`, `debugger:` and `remote:`:

- `src/lib/nogc_sync_mut/terminal/power/t32_power.spl` (4 sites)
- `src/app/test_daemon/adapters/hardware_adapter.spl` (1 site)

None of the four `class DebugConfig` declarations in the tree has any of those
fields — they are `host / port / target / program / options`. All five were
replaced with the existing declared-field helper `DebugConfig.for_trace32()`.

The `FunctionOutline` / `type_params` spelling in the title is the same defect
class on a different literal, surfaced earlier in the session; lowering reports
only the first offending literal, so the errors appear one at a time.

**No rebuild or redeploy was needed** — `src/lib/**` and `src/app/**` are read
as source on every process start, and the fix is source-side.

### Why it was hard to locate

The diagnostic names the struct and the field but not the construction site,
and the `[in <file>]` suffix is the compilation unit (the runner entry), not
the offending file. Fixed forward in
`src/compiler_rust/compiler/src/hir/lower/error.rs`: `CannotInferFieldType` now
appends `(declared fields: ...)` when the declared set is known (the literal
path always knows it), turning an unlocatable fleet-wide de-optimisation into
an obvious typo report. That half is Rust-seed side and **only takes effect
after a seed rebuild + redeploy**; it is a diagnostic improvement only and is
not required for the throughput fix above.

### Regression guard

`test/01_unit/lib/debug_config_literal_fields_spec.spl` — asserts no
`DebugConfig` declaration carries `args`/`debugger`/`remote`, that neither fixed
file reintroduces those literals, and that both use `DebugConfig.for_trace32(`.

## Suggested next steps (historical — superseded by "Root cause")

1. Locate the `FunctionOutline` struct reached from
   `src/app/test_runner_new/main.spl` and give `type_params` an explicit type
   annotation (workaround), or
2. Fix HIR lowering field-type inference for the construct involved (root cause).
3. Reproduce hard-failure with `SIMPLE_JIT_STRICT=1 bin/simple test <any spec>`
   to get the precise lowering site.
