# Seed native BDD interception discards imported callbacks

Status: confirmed actual native failure; source repair is unverified, focused Rust criterion CLOSED/HOLD after three bounded attempts. Bug DB reconciliation pending: no qualified writer available. Canonical ID: `seed_native_bdd_imported_callback_discarded`.

## Actual failure

Producer: immutable d958 seed (`d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`), explicitly authorized Phase1 bootstrap diagnostic. Real native artifact: `build/native_probe/aggregate-native-owner-20261012-sol/final3/framework.exe`, SHA-256 `30cdaddafcca95c9e87bbc7f850a9f6b1dbfb110f059340ee752715c2c1de21a`.

Supported native archive build compiled41/41 modules, followed by strict linkage with the pinned core-C donor and real generated entry/initializer graph. No-argument exit90 and scalar/text/UTF-8 argv/array/value-returning-callback ABI sentinel passed. The deliberately failing registered-case sentinel instead returned2 (infrastructure failure), printed `0 examples, 0 failures`, and wrote an owner ledger with zero cases. No declaration or completion record exists. All stages ended Job0; source/tool/runtime pins remained unchanged. This executable is built but has executed zero real aggregate cases. The eight framework behavior checks were not dispatched after the sentinel failed.

Source trigger, already present in the native fixture:

```simple
use std.spec.{describe, it, expect}
fn failing_case():
    expect(7 * 6).to_equal(43)
fn register_case_failure():
    it("body result", failing_case)
```

## Causal evidence

Saved `final3/case-registration.disassembly.txt` includes actual COFF relocations. The compiled registration function calls `rt_bdd_it_start_rv`, allocates a closure pointing at the genuine `failing_case`, then calls `rt_bdd_it_end(1)`. It neither invokes that closure nor calls the imported `std.spec.it` owner. Consequently the real registry does not declare or execute the case.

Saved `final3/describe.disassembly.txt` proves the actual imported `std.spec.describe` body includes indirect callback calls. This is not evidence that all void callbacks are broken. The source statement interception explains why `it` was redirected while the outer describe expression, in a different expression position, reached its real owner.

The committed Rust baseline `2fbcf0cf3e01ed48ec3f4952a030fae89858a6e2`, at `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`, calls `try_lower_bdd_statement` before ordinary expression lowering. That helper matches bare identifiers by spelling, including `it`, without first honoring lexical/import bindings. `lower_bdd_body` handles Lambda/DoBlock specially but merely evaluates an ordinary named-function expression. The observed native closure allocation followed by unconditional end(1) matches this fallback exactly. Baseline source is explanatory evidence, not a claim that every baseline line is embedded in d958. A separate working-copy binding repair is unverified and is excluded from this report's admission.

## Repair requirements

Honor the resolved callable owner before either BDD statement or matcher interception. Imported `it`/`describe`/`expect`, local declarations, local callback parameters and owner-qualified flattened imports must go through ordinary call lowering. Existing unbound BDD syntax may retain its intentional intrinsic behavior. Do not rename imports to evade the compiler, force assertion success, route all bindings through a global bare-name table, or invoke an imported callback while still bypassing its registry owner.

The native compiler already supplies a per-module `qualified_import_functions` map built from that module's actual use statements (`native_project/compiler.rs`). Flattened imports have separate owner-qualified binding metadata. The fix should reuse those authorities and lexical lookup rather than guessing from any function with the same name in the whole program. Guard matcher interception too: otherwise an imported `expect(...).to_equal(...)` still updates the wrong framework.

Focused acceptance for the new compiler feature: resolved imported/local/local-parameter calls remain HIR Call expressions and preserve the exact owner; named void callbacks execute once; lambda and block callbacks retain behavior; imported matchers reach the actual expectation owner; unbound intrinsic BDD forms retain start/body/end and genuine failure semantics; duplicate same-named functions in unrelated owners do not suppress a real unresolved intrinsic. Then a rebuilt producer must make this existing native sentinel declare one case, execute it, record failure and return1. No fourth unchanged aggregate fixture build is authorized.

## Pure-Simple comparison

Bounded search of `src/compiler` found no counterpart emitting `rt_bdd_it_start_rv` or `rt_bdd_it_end`; only BDD text-ABI declarations exist. Current pure MIR statement lowering delegates expression statements to `lower_expr`, and `_MirLoweringExpr/expr_dispatch.spl` delegates `HirExprKind.Call` to normal call lowering (apart from explicit enum constructor handling). The analogous source interception bug is not established in pure Simple. Pure producer native callback/registry parity remains unrun; do not add a speculative pure workaround.

The earlier seed interpreter BDD named-callback rejection is separately documented. Its three-cycle source criterion and this three-cycle native dependency criterion remain closed. Six requested full native products remain0/6 qualified, and their original runtime cases remain UNRUN.

## Focused Rust regression status

Evidence packet: `build/native_probe/seed-native-bdd-binding-20261012-sol`. The first two bounded Cargo attempts reached zero tests because the immutable source capsule omitted committed C headers. They are infrastructure failures, not semantic RED. The complete follow-up closure audit added 15 exact committed inputs; preprocessing all 27 C inputs selected by the committed Windows runtime build succeeded. No unrelated dirty Rust owner was copied into the capsule.

The final third cycle builds the unchanged production baseline with 12 real Lowerer regressions, runs each once, and requires the expected imported-callback assertion failure before applying the exact candidate owner in a separate source capsule. A candidate run is permitted once only; any infrastructure failure, timeout or unexpected baseline result closes the feature HOLD. Existing Cargo artifacts remain under Cargo's source/feature/compiler validation; no fingerprints or cache identities are rewritten.

The focused matrix covers imported named callbacks, imported matchers and hooks, imported colon-block callbacks, local functions and parameters, alias/re-export and qualified imports, unbound intrinsic bodies, unrelated owner declarations, and exact current native-module import precedence over a foreign flattened declaration. A tagged foreign function must not inherit the entry module's native import map. Unique foreign module-global variables lack sufficient owner metadata for a new blanket binding guard; that broader case is not claimed as covered. These are HIR checks, not native callback execution or performance qualification. Native hook ordering, deliberate assertion exit, producer rebuild and six-product qualification remain outstanding.

Final cycle3 ended with timeout exit124 after904.7297 seconds including collector closure, peak2,627,232KiB and finalJob0. Source/tool pins were unchanged. Cargo produced the genuine compiler library and `native_bdd_binding-5095d5735ceb35e7.exe` (11,638,272bytes, SHA-256 `dab332e947a97de53d7c44cdc2f6577cfbc225fbe76db8b878d4eaf6b574e4ee`) but did not finish the required unit-test artifact closure. Per the agreed infrastructure-stop gate, zero of12 HIR tests executed and the candidate was not applied to a test capsule. Artifact presence is not semantic RED or PASS. The actual compiler/dependency cache and every receipt are preserved; no fourth Cargo attempt is permitted under this criterion. `TERMINAL_EVIDENCE.json` and `CYCLE3_RESULT.json` contain the terminal facts. The original2GiB reservation underestimated observed peak; a4GiB future-admission observation was recorded without changing the live guards, and all reservation was released after Job0. No native performance conclusion is supported.
