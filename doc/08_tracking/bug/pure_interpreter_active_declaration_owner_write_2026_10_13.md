# Pure interpreter active declaration updates across module owners

Status: private source-owner behavior repair observed; native, Rust parity and broader lifetime/performance qualification remain HOLD. Three diagnostic cycles closed; do not replay the seven passing criteria.

## Actual failure and changed behavior

The current pure evaluator owns `eval_current_decl_id` in `src/compiler/10.frontend/core/interpreter/eval.spl`. `coverage_owner_file()` and `eval_caller_file()` use it to select the currently executing declaration's defining module. Function/method entry and restoration previously assigned that scalar directly from sibling `eval_calls.spl` and `_EvalOps/call_method_eval.spl`. Imported source parsing also changes `module_get_path()`, so falling back to that path can select an imported module instead of the active caller.

The first diagnostic failed `undefined variable: left`; its verbose duplicate-dispatch stream exceeded the existing inner capture limit, so its strict verdict remains HOLD. The second used a coherent private current-source projection and the namespace/schema candidate, but retained those cross-owner scalar writes. It observed four failures: undefined `left`, undefined `functions`, undefined `LocalReceiver` after an import, and undefined `hidden` instead of the required private-constructor denial. Three distinct real criteria passed: ordinary method dispatch, real parser `DECL_IMPL` target/body plus same-owner append replacement, and stale instance rejection after an actual AST reset recycled a declaration slot.

The final private change introduces eval-owned getter/exchange functions and routes all three call/method entry-restoration pairs through that owner. It retains the failed assertions unchanged and adds bounded route diagnostics. All four passed: original two-owner methods produced **107209**, namespace function **712**, lexical receiver shadowing **617**, and a private constructor was denied with the expected reason. Seven route witnesses show the active caller and declaration owner remain the entry file while the parser's module path points at imported files. The local receiver's actual slot/value takes precedence over a same-spelled namespace alias.

This supports the owner-controlled state repair for this observed producer/source cut. It does **not** establish that direct imported scalar assignment is forbidden language syntax. The discrepancy remains a language/runtime parity issue: a future independently scoped reproducer must distinguish imported-write semantics from provider-selected binding behavior and mirror any required repair in pure and Rust owners. Current Rust source is not authenticated as the retained binary's build source; no specific d958 implementation algorithm is inferred.

## Reproducible evidence

Control packet: `build/native_probe/selected-schema-ownership-20261013-astra`.

- Candidate 2 result: `C:/simple-probes/owner-identity-candidate2-20261013/attempt/RESULT.json`; SHA256 `555fb59a6f551774929d4438207e83914cc177663eb7c8c2d1594834917bc201`. Receipt `1b21db238e0cec64947151a8bc2bae7de65bfe95cbd7cb8144a8a98d70e88662`, exit 1, final Job 0, trusted 7 executed / 3 passed / 4 failed, truncation false.
- Final candidate patch `integration-v7/CANDIDATE.patch`: SHA256 `409ca0a48681b34d653affb02781efaa4eade41b2b9bd667e77d8f7fbb6e1bed`. Caller-owner delta `f93e31728bbf7d37251ae06b9fbe5782f3e33c95d477da16d71ee7918bbd221e`.
- Final source manifest `CANDIDATE3_SOURCE_PINS.json`: SHA256 `c4da3c5e93fca88bb7227b802ebbbcca0ca4bbeac8de415fff7beea5ad395d47`; private Git `f49c11d81b6db4710464b195e6facd4e7f71de2c`, descendant of the coherent 13,756-file current-source cut.
- Final four-case fixture: SHA256 `b97d7136a70c34b6c2ba24137d3a5255a5acccbf3dbf205fe11524013ffa6f61`; runner `95b0158cad033c44544a10b4f2acda9f5ccdba03988aeb91c37a69e6fc86e922`.
- Final result: `C:/simple-probes/owner-identity-candidate3-20261013/attempt/RESULT.json`, SHA256 `b77ade058afde4d46eab5d664287ac494f972d910aaf2fa1ee488d7d7af15172`; receipt SHA256 `5511d1dc4c07c5a6eb86cef318dd67ee94b90f76bc14f16cf9d823ba9e19e1f4`, exit 0, final Job 0, trusted 4 executed / 4 passed / 0 failed, truncation false. All 15 required owners were actually read; outside and changed input reads were zero. `fixture_read=false`: the trace did not authenticate the entry fixture read, despite its pre/post hash and the observed named assertions. Bootstrap diagnostic producer SHA256 `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.

The seven criterion passes are the union of two separately bounded executions, not a claimed combined seven-case final run. The first three were not repeated.

## Remaining qualification

No shared production source was changed. The source candidate's full module-generation/reload contract, captured imported dependencies, Rust representation, value-struct copy behavior, private/package/friend visibility breadth, and native compiler/tool integration remain incomplete or unqualified. Reused value-slot schema bookkeeping also needs a sparse-metadata design and measured memory/performance evidence; no no-regression claim is made. Actual source-read pins do not authenticate the embedded provider's selected body digest. Diagnostic print instrumentation is private and is not a proposed production trace API.
