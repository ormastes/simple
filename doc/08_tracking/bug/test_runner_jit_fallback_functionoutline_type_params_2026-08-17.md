# test_runner JIT fallback: `Cannot infer field type: struct 'FunctionOutline' field 'type_params'` drops the whole runner to the interpreter

- **Date:** 2026-08-17
- **Status:** OPEN
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

## Suggested next steps

1. Locate the `FunctionOutline` struct reached from
   `src/app/test_runner_new/main.spl` and give `type_params` an explicit type
   annotation (workaround), or
2. Fix HIR lowering field-type inference for the construct involved (root cause).
3. Reproduce hard-failure with `SIMPLE_JIT_STRICT=1 bin/simple test <any spec>`
   to get the precise lowering site.
