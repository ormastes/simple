# Native function owners and optional struct coalescing

**Status: Linux native callback and adapter ABI checks passed.** Windows callback validation and canonical bootstrap admission are still pending. The user authorized the continuation after the prior three-cycle stop.

## Production evidence

Frozen main `d9281560d8f3d84687cbc50ea25eeff4d62c3c33` failed strict bootstrap verification on both hosts.

- Linux full CLI compiled 2489 files with zero compile failures. The retained object for `plugins/backend_registry/full_static_backend_ports.spl` defines owner-qualified `_gpu`, but references bare `_gpu` from four function-value assignments.
- An ordinary private `spl_language_manifest` definition was kept bare by the definition mangler's blanket `spl_` exemption; an imported caller references its module-qualified owner.
- Windows run5 emitted 22 unresolved-symbol stubs despite `SIMPLE_NO_STUB_FALLBACK=1`. The run was stopped and its executable rejected. Its output is diagnostic evidence, not an admitted compiler.
- Four stub names (`rt_hal_unavailable_spawn/join/cancel/effect`) are ordinary Simple functions assigned to function slots in `parallel_executor.spl`, rather than missing external runtime providers.
- Seven stub names are fields of `RtHalIsolatedHostPort`. Those calls use inferred `rt_hal_host ?? rt_hal_unavailable_isolated_host()` bindings. The explicitly annotated `join_exact_until_fn` call did not appear in the stub list.

## Cause and scope

Function-value references use MIR `GlobalLoad`/`GlobalStore`. Their mangling previously skipped runtime-looking names and relied on suffix lookup instead of lexical function ownership. Imported same-suffix candidates can make that lookup ambiguous. Resolve real local globals first, then local functions, before runtime/suffix fallback. Explicit external, export and global ABI names retain their existing contracts.

HIR's `local_globals` set also contains function and type symbol metadata. MIR copies that set but excludes functions from its `globals` data declarations. Checking the metadata set alone incorrectly treats functions as real data globals. The precedence guard therefore uses the intersection of declared MIR globals and local metadata. A regression lowers the actual callback fixture before mangling and checks both this distinction and the resulting owner-qualified references.

Definition mangling must not infer an external ABI from the spelling `spl_` alone. Ordinary private Simple functions have module owners; actual extern declarations and explicit export/global attributes keep bare symbols. The canonical `main` to `spl_main` entry ABI remains.

The existing MIR callable-field implementation already emits `FieldGet` plus typed `IndirectCall`. It accepts a concrete struct receiver. Optional struct coalescing retains `SharedPointer<Struct>` metadata, which prevents that implementation from recognizing the fields. The prior array correction narrows only arrays. A precise imported HIR regression records this failure before any struct correction.

No app annotations, invented providers, unresolved-symbol stubs or duplicate callable-field dispatch are acceptable fixes. Scalar optional payload rules remain separate because tagged and raw scalar representations differ.

## Executable regression

`compiler/tests/native_symbol_owner_binding.rs` lowers the real three-file `test/fixtures/native/symbol_owner_binding` import closure and checks nominal struct metadata plus typed indirect calls. It then builds and executes the same fixture using `NativeProjectBuilder` under bootstrap and strict-stub flags.

The fixture covers imported private `spl_*`, local `_gpu` and `rt_*` function values, optional struct nil/present cases, annotated control, callback state and return values, one receiver evaluation, a real method control, and the real external `spl_ordered_key_cmp` ABI. Mangler unit tests cover imported suffix ambiguity, actual-global precedence, explicit ABI exports and the entry ABI.

Results are recorded in task evidence after execution. No Stage2 or Stage4 pass is claimed by these focused tests.

The actual pre-fix imported HIR test failed with coalesced type `TypeId(24)` (`SharedPointer`, inner `TypeId(16)`) while both the imported struct and concrete fallback had type `TypeId(16)`. After the struct-only correction, HIR/MIR passed one test with zero failures or ignored cases. Struct narrowing requires the default to have the same concrete inner type; nil and optional defaults keep the wrapper. Existing array behavior and scalar boxing rules are unchanged.

## Callback ABI continuation

The retained binary proves the owner binding is correct: `make_gpu_port` stores `probe__ports___gpu` at address `0x402690`. Its caller passes the callable record in RDI and the text argument in RSI, while the named function expects its text in RDI. LLVM's indirect-call path always prepends a closure context, but the named-function record points straight at the ordinary function. The integer callback has the same argument shift.

The existing direct-function marker at record offset 8 cannot safely distinguish these records inside LLVM indirect calls. Captured closures store their first user capture at the same offset, and a captured integer can equal the marker. C thread and Rust executor dispatch already have this sentinel ambiguity; that existing runtime limitation is a separate follow-up. This correction leaves their dispatch and the Cranelift boxed closure path unchanged.

LLVM named-function values now point at private C ABI adapters which discard the implicit context and call the original function with its exact parameter, return and calling-convention types. Both local function-value loads and global function initializers emit zero-capture records with zero at offset 8. Ordinary indirect-call lowering and captured-closure layouts remain unchanged. Adapters handle void returns and reuse only generated adapters identified by target metadata. Constant-time preferred-name lookup and deterministic numbered collision names preserve user symbols without scanning every module function on each load.

New controls cover adapter native signatures and void calling conventions, named global callbacks, zero-capture closures, and a captured integer equal to the old direct-function marker. The failed native fixture is the runtime acceptance criterion. Earlier passing mangling, HIR/MIR, strict Windows link and SQLite SDK criteria will not be repeated.

Retained disassembly: `build/mini_builds/callback-abi-review-20260929/retained-probe-disassembly.txt`, SHA256 `3aa7b80a8704747eb23d83b8894793118f94db9a5d8de53f974de49f3b95fe55`. Continuation cycle 1 passed the actual native fixture (1 passed, 0 failed, 0 ignored) and the new LLVM adapter ABI test (1 passed, 0 failed, 0 ignored). Source-input hashes remained unchanged. Evidence: `/mnt/simple-bootstrap-6b2/callback-abi-tests-20260929/cycle1/`; retained executable SHA256 `e0ee47180c7141f2fa4f7fd395196e56c74bdb76509451b9eeff354d986b1c75`. The native check executed all previous assertions plus named global callbacks, zero-capture closures and the captured-marker case.

## Previous recorded results

The first native attempt failed linking bare `_gpu` and `rt_hal_unavailable_spawn`, exposing the local function metadata distinction above. After correcting the guard to use actual data declarations, the final native link succeeds. At that earlier checkpoint, runtime behavior remained unresolved.

| Check | Recorded result |
| --- | --- |
| Six mangler ABI/ownership controls, production cycle 2 | 6 passed, 0 failed, 0 ignored |
| Actual imported struct HIR/MIR, production cycle 2 | 1 passed, 0 failed, 0 ignored |
| New regression from actual callback source lowering and mangling, production cycle 3 | 1 passed, 0 failed, 0 ignored |
| Native fixture compilation, production cycle 3 | 3 compiled, 0 reused, 0 failed |
| Native fixture link, production cycle 3 | PASS; 42 KB executable via clang |
| Native fixture execution, production cycle 3 | FAIL; executable exit 1, empty stdout/stderr; first callback returned false |

The final callback regression proves that actual function-value references retain their module owner. The earlier six controls and HIR/MIR check were not repeated. Passing compilation, linking and type assertions do not establish callable runtime behavior; later assertions in the native fixture were not reached. Cargo reports test exit 101 for the execution failure.

Local evidence is retained on D-backed storage:

- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/hir-red-cycle3/`: actual pre-fix shared-pointer type failure.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/green-cycle2/{mangle,hir,native}.log`: six controls, imported HIR/MIR pass and the preceding native link failure.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/green-cycle3/{causal-mir,native}.log`, `inputs.sha256`, `result.env` and `probe.sha256`: final checks and exact inputs.
- `/mnt/simple-bootstrap-6b2/symbol-owner-fix-tests-20260929/tmp/.tmpxpT4RR/probe`: retained failing executable and adjacent native cache. SHA256 `150c3948f75cdb4c46a348fd0e6fbb6c0840e5d3ead95abd9119ea8bc50030d3`.
- `D:/dev/simple-bootstrap-bootstrap-tools-fix-20260929/build/mini_builds/symbol-owner-review/final-cycle3-owned-inputs/`: immutable snapshot of eight tested owned files, scoped patch and hash manifest. This results update is a documentation-only addition after that snapshot.

Three production verification cycles were used: cycle 1 stopped at a peer test import compile error; cycle 2 passed the controls/type check then failed native linking; cycle 3 passed the actual callback ownership regression and native link, then failed execution. Earlier test-compilation repairs were recorded separately. Work stopped at that checkpoint. The subsequent user-authorized continuation and its results are recorded above; the earlier failed executable remains preserved. Canonical bootstrap admission has not yet passed.
