# Compact declaration providers omit imported callable RTI rows

Status: reproduced with the exact phase2 compiler; targeted source repair authored, runtime verification pending a rebuilt producer.

The phase2 compiler `/tmp/scv-phase2-current-rebase-20261027/phase2/simple` (SHA-256 `9d202a662186f5e478381465ca357f259a84a5910285256a0945c2577fb2f73f`, compiler source `5b04d099c7891b4ed0396e80e5c3e56f4310e741`) rejects a two-module imported Optional record match. The same compiler compiles and executes a local Optional i64 control, printing `42` and exiting zero. The original RR publication fixture reaches 71 MIR modules, with 59 successful and 12 failed; this report does not claim that one repair clears all independent owner-graph diagnostics.

Evidence root: `/tmp/retained-enum-owner-20261027`. `primitive/result.sdn` is the successful control; `imported/compile.log` retains the minimal failing operation. Both use the recorded bootstrap hosted runtime authority and bounded process-tree supervision (300 seconds, 4 GiB). The guard reports `enum match expression and retained Result/Optional declarations conflict` at the imported fixture's direct `match maybe()`.

The final debugger observation (`owner-keys-complete/gdb.log`) records the retained key as `optional(struct(<exact provider>::Payload)[])` and the expression key as `i64`. The earlier two debugger configurations stopped on shell helper termination before MIR and are diagnostic harness attempts, not compiler-test results.

The failure is a missing native integration path. `enum_match_expr_type` queries the return-type interface before raw callee metadata. Full HIR prescan publishes provider RTI rows, but native compilation uses body-free `MirHirModuleDeclarationsV1` providers. `prescan_declaration_callables_v1` had an explicit TODO for their RTI registration. Consequently an imported provider row is unavailable before entry-module MIR and the expression path accepts a scalar signature fallback, while call lowering separately retains the exact Optional record owner. The existing conflict guard correctly refuses those incompatible declarations.

The proposed repair adds a shared body-free callable-signature API in the HIR RTI owner and publishes compact provider rows before consumer MIR. It keeps provider-owned SymbolIds on the provider side, transports stable DeclRef identity, and binds into the consumer table through the existing RTI binder. Full HIR and compact declarations share the same row conversion. It preserves generic parameter ordering, explicit annotation rules, and the existing mismatch/ambiguity guards. No RR consumer workaround or guard relaxation is included.

Authored regressions cover body-free/full-HIR Optional record row equality and symbolic generic preservation; `test/fixtures/compiler/retained_optional_owner/imported.spl` is the actual executable regression. The local primitive control is retained and must not be rerun unchanged. These new source regressions have not been executed against the repair: the currently frozen compiler predates it. Qualification requires a new producer, its exact Hello compile/run gate, then the failing imported fixture with expected output `42` and zero exit. Only after that should the RR owner attempt one changed producer-bound fixture build. Preserve all original failed receipts.

## TDD evidence and remaining green gate

The original `imported.spl` Optional record regression failed on the old exact compiler before the repair was written; its successful local primitive control is retained without a rerun. Additional independently executed old-producer cases now live under `/tmp/retained-enum-owner-tdd-red-20261027`:

- `result_record`: RED with the same imported Result/retained declaration conflict.
- `duplicate_owners`: RED at both calls; two distinct provider modules each declare `Payload`.
- `generic_owner`: RED earlier at method lookup, `E-RTI-004: no local symbol for id 1125899906842624`. This independent generic nominal-ID boundary is not claimed repaired by the compact registration change.

`test/01_unit/compiler/mir/declaration_return_types_v1_spec.spl` adds three direct compact-prescan integration examples. It projects actual encoded HIR bytes through the existing transient owner and calls the production compact callable prescan. It covers Optional/Result rows, same-named provider declarations in separate symbol tables, and owner generic method parameter retention. These are authored, not executed; they are distinct from the converter-only tests.

Green qualification remains OPEN. Freeze the reviewed source into a new producer; verify that exact producer with real Hello execution; then execute the previously red imported Optional, Result, and duplicate-owner fixtures and collect the generic case's actual new boundary. Each fixture expects `42\n` and exit zero. Record raw process results and exact producer/runtime/fixture hashes. No old compiler rerun, helper row equality, source review, or existing unrelated Hello receipt establishes green for this change.
