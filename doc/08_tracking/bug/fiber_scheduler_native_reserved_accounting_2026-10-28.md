# BUG-ASYNC-FIBER-RESERVED-NATIVE-20261028: admitted fibers retain zero reserved bytes

**Status:** OPEN, native diagnostic failure; root cause unisolated.
**Observed:** 2026-10-28. **Source baseline:**
`3e1a1b611357f2c34285b9bf595c186f77cb7de8` plus the named fixture.
Do not infer a particular compiler pass is responsible from this observation.

The existing production owner
`src/lib/common/task_runner/fiber_scheduler.spl` receives a budget of30 and
two estimated resources10 and20. The native fixture observes both estimates
correctly and admits two ready fibers, but `reserved` remains0 instead of30.
The source `_fs_admit_head` adds each estimate to `t.reserved`; whether native
indexed arithmetic, record-field mutation/return, or another boundary loses
the update remains to be isolated. This failure exists before the voluntary
yield fairness change.

```text
submitted budget=30 est0=10 est1=20 error=
admitted reserved=0 ready=2
first fiber=1 reserved=0
yielded reserved=0 ready=2
```

The regression fixture is
`test/fixtures/async_resource/fiber_yield_progress.spl`. It separately checks
ready-peer progress, four peers across three yield rounds, park/wake state,
terminal inventory and resource accounting. After the fairness correction,
both progress groups pass but17 accounting checks fail; aggregate exit is12.
No assertion was converted to a pass. Accounting failures accumulate so they
do not hide the independent progress assertions; the executable remains FAIL.
Canonical SSpec assertions remain exact expected-byte assertions and UNRUN.

## Exact diagnostic provider and evidence

- Compiler-only phase2 path:
  `/tmp/simple-retained-rti-producer-20261027/phase2-owner-proof/frozen/simple`.
- Compiler SHA256:
  `8d21317328ccb2b32ba707d2485c3c8ca6c4d02592952537e7754a6d006cb116`.
- Target/backend: `aarch64-unknown-linux-gnu`, Cranelift,
  `core-c-bootstrap` runtime bundle; **DIAGNOSTIC_NOT_ADMITTED**.
- Raw compile/execute logs and watchdog receipts:
  `/tmp/simple-async-yield-evidence-20261028/`.
- [Structured evidence](../../03_plan/evidence/async_fiber_yield_progress_2026-10-28.sdn)
  records source/fixture/binary/runtime hashes, exact outcomes and cache caveat.

Five bounded compile/execute diagnostic cycles were used: initial accounting
failure, state trace, estimate trace, isolated fairness RED, corrected fairness
with accounting still failing. No further unchanged retry is scheduled. The
separate lockless-map draft's exhausted six-cycle history is not reset here.

The2-module native closure consumed3,532,448–3,930,540KiB peak observed RSS.
This is a concrete build-overhead observation, not an admitted steady-state
runtime benchmark. The first command's `--cache-dir` did not isolate global
HIR storage; its log reports a refused cache-cap write and continued uncached
compilation. Later commands set explicit private cache environment paths.
Do not delete other sessions' shared caches or raise their caps to hide this.

## Closure criteria

Isolate the smallest field/index/return boundary reproducer, fix its actual
owner, and run the original expected30/20/0 accounting assertions on a compatible
exact-source native producer. Retain the independent fairness regression.
Required SSpec/manual, core/MCP and bootstrap gates remain open until the
appropriate admitted runtime exists; this compiler-only fixture does not
qualify TestRunner, general async ResourceFactory, multicore execution or a
strict lock-free path.
