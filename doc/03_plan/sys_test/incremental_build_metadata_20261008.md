# Incremental metadata acceptance and performance plan

<!-- codex-design -->

Status: proposed executable SPipe scenarios; no scenario below is reported executed. Production interfaces must exist before generating real executable specs. Do not add placeholder passes or use source-text matching as proof of runtime behavior.

Proposed executable entry: `test/03_system/app/compiler/feature/incremental_build_metadata_spec.spl`. Mirrored manual: `doc/06_spec/03_system/app/compiler/feature/incremental_build_metadata_spec.md`. The implementation owner supplies real fixture builders and bounded native/process evidence, then generates and reviews the manual. Existing source-only candidate tests remain separately labeled UNRUN.

| Scenario | Requirements | Actual assertion / fault injection |
| --- | --- | --- |
| Standalone fallback | 001,004 | Compile/run with Git, SCV, runner and daemon unavailable; compare outputs and diagnostics with managed path |
| Equivalent edits | 002,003,012 | IDE/Spipe/SCV adapters produce equal canonical semantic delta digests for identical UTF-8 transitions; audit origins differ |
| Snapshot separation | 003,013 | Buffer/index/worktree/commit differ; only exact requested snapshot receives matching receipt |
| Header-only imports | 005,006 | Instrument opens: unchanged imported SPL bodies and private AST are not read; selected generic/CTFE bodies have explicit digest reads |
| One publisher | 006,007 | Concurrent same-key requests publish once; different config keys remain independent; waiters receive immutable identical outputs |
| Header before object | 006,007 | Delay backend; dependent frontend resumes from validated header while link waits for object |
| Header survives object failure | 006,007,011 | Fail/crash object emission after header commit; header receipt remains valid and reusable while object/link qualification fails; retry only the missing object stage |
| Diagnostic observer coverage | 005,016 | Interface-only does not read ordinary dependency bodies or claim full diagnostics; full-diagnostics rejects absent/stale body receipts and validates missing bodies; matched coverage reproduces baseline diagnostics |
| Import cycle | 005,007 | Two-module SCC resolves declarations without waiter deadlock or partial summary publication |
| Invalidation matrix | 008 | Body edit, public signature, exported constant, initializer/effect, added overload/impl/aspect/module, negative lookup and guard flip match fresh builds |
| Cross-host artifact boundary | 009 | Portable AST byte round-trip; target/layout mismatch rejects object reuse; no process-local IDs in serialized data |
| Crash and reclamation | 007,012 | Crash before/after commit, stale owner epoch, abandoned waiter, pinned-object GC, torn journal and watcher overflow remain safe |
| Binary-first qualification | 010,011 | Binary usable while residual work pending; failed/missing/stale mandatory receipts keep CI/release nonpassing |
| Scope completeness | 008,011 | Hello-only receipt cannot certify project; deletion/new membership changes inventory; duplicate counts cannot satisfy completeness |
| Receipt/note races | 013 | HEAD moves while old job completes; old receipt binds only old commit; concurrent note writers preserve typed records |
| Storage parity | 014 | Packed and hybrid artifacts link/run equivalently; missing/corrupt CAS member causes miss/failure, not false readiness |
| Continue to end | 015 | One compile failure and one crash do not suppress independent tasks; successful object reused; only unknown crash tasks isolated |
| Performance/memory parity | 016 | Same semantic outputs, diagnostics and failure classifications; bounded memory/queues; actual p50/p95 timing and bytes recorded |

Shared manual flow names: `step("Freeze the requested source snapshot")`, `step("Acquire one verified summary action")`, `step("Publish the binary before residual checks")`, `step("Join mandatory qualification receipts")`, and `step("Recover without certifying stale artifacts")`. Use real built-in matchers and artifact/exec/log captures. Never describe an authored fixture as a run.

## Formal verification plan

Implement a finite transition model with two generations, two publishers/readers, header/object stages, pins and crashes. Check the ten safety properties and conditional liveness obligations in the detail design. Bound the explored state space and retain counterexamples. Model-check status starts UNRUN. Native concurrency/failure tests are required in addition; the finite model does not prove semantic read-set completeness. The Astra review's META-01–20 cases form additional concrete fixture coverage, including materialized checkout policy and incompatible guard IDs.

## Performance matrix and measurement boundaries

The user's target is <=100 ms for compiling one representative small changed SPL to an object with warm, valid dependency summaries/runtime prerequisites, excluding independently scheduled dependency compilation and final executable linking. Include process startup, snapshot admission, summary validation, parsing, lowering, code generation and object publication in that measurement. Report cold-start and executable end-to-end results separately; do not relabel a hot daemon result as standalone startup.

For the strict benchmark, no entry object is reusable: exactly one real entry object must be generated, and zero imported-body codegen may occur anywhere in the process tree, including background children. Dependency preparation is completed and recorded before measurement, not hidden behind the timer. A required generic/CTFE body triggers a separately classified supported-body workload or explicit fallback, never silently omitted semantics. The ordinary build may schedule dependency work concurrently; its full work and end-to-end time are reported separately.

Record p50/p95 elapsed and CPU time, peak private/tree RSS, bytes read/hashed/copied, file opens, child processes, lock wait/hold, cache miss reasons, module counts and actual object/executable counts. Run a bounded sample set once per unchanged candidate, not repeated green validation loops.

| Workload | Required performance/correctness observation |
| --- | --- |
| Warm no-change | Zero source-body parses, HIR/MIR lowering or object emission when admitted inputs match |
| Warm small body edit | Target <=100 ms p95 under the stated fixture; dependent rebuild count remains zero only when actual read facets permit |
| Public or guard edit | Exact affected closure matches uncached reference; no latency target excuses missed invalidation |
| Cold compile/full bootstrap | Full costs reported, including snapshot, source inventory, runtime C preparation and toolchain hashing |
| Post-build enqueue | Proposed <=10 ms p95 local durable scheduling overhead; benchmark before adopting as a gate |
| Parallel 1/4/20/40/80 requests | One publisher per key, no lock-storm admission failures, throughput/RSS scaling and waiter fairness |
| 128 logical HIR tasks | Scheduler correctness independent of configured execution capacity; no hard-coded 20-worker semantic limit |
| Daemon/cache loss | Bounded fallback gives correct output; its slower result is classified honestly |
| Toolchain change | Compiler/DLL/same-size replacement invalidates; duplicate initial hashing removed without dropping final validation |

Tentative 100 ms budget: startup/admission 20 ms, headers 10 ms, parse/lower 30 ms, backend object emission 30 ms, publication 10 ms. These are allocation targets, not measured promises. Trace any overrun to its phase before changing the budget. Macro/CTFE-heavy modules, LLVM optimization/LTO, cold source capture and final link need separately declared workload targets.

Memory acceptance uses the same inputs and workload size before/after: no unbounded journal/AST retention, no artifact-sized buffer just for hashing/header checks, no per-waiter payload copies, and no correctness regression under cancellation/GC pressure. Structural sharing must retain roots until the last reader releases them.
