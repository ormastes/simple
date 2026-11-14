# Mandatory MIR target session: entry and prescan inventory

Pinned draft #9222 head: `f9aec70168c47e8bb709b43c503e81ad54a09439`, rebased on release `3e0584c314e`. This is a documentation prerequisite for the accepted [immutable HIR / TargetHIR / MIR plan](immutable_hir_targethir_mir_refactor_plan_2026-11-03.md), not implementation or qualification. No source or tests were changed or executed for this inventory.

Scope: named `MirLowering` entry families and their direct production callers in `src/compiler` and `src/app`, with targeted executable-spec callers where a production caller was not found. Receiver construction was checked to exclude identically named `HirLowering.lower_module` calls. This is not whole-program call-graph proof; reflective/native name dispatch, all test callers, and every internal helper are not exhaustively enumerated. Line numbers below refer to the pinned draft.

## Owners and current return contracts

Abbreviations: **ML** = `src/compiler/50.mir/_MirLowering/module_lowering.spl`; **DP** = `src/compiler/80.driver/driver_pipeline_lowering.spl`.

| Entry | Current return | Direct caller / boundary |
|---|---|---|
| `ML:2777 lower_unfrozen_module_v1` | `Result<MirModule,text>` | Explicit verification producer, `verification_call_lowering_v1.spl:68`; validates carrier/current/constructor-bound context, then calls raw entry at ML:2789 |
| `ML:2792 lower_module` | `MirModule` | Internal bootstrap entry ML:2432, transient fallback ML:2541 and active-scope call ML:2561, unfrozen adapter ML:2789; external callers listed below |
| `ML:2817 lower_module_guarded_v1` | `MirModule` | Only direct production caller found is ML:2801, after trace entry and `apply_decl_cfg_guards` |
| `ML:2414 lower_bootstrap_entry_module` | `MirModule` | DP:1175; driver mutates/publishes returned MIR before collecting lowerer diagnostics |
| `ML:2435 lower_bootstrap_closure_module` | `Result<MirModule,text>` | DP:1160; delegates to transient wrapper at ML:2460 |
| `ML:2462 lower_module_transient_scoped` | `Result<MirModule,text>` | DP:1647 direct path, DP:1799 fallback, ML:2460 bootstrap closure. Scope refusal calls raw entry; successful scope acquires journals and calls raw entry before promotion/publication |
| `archive_borrowed_module_v1.spl:33 lower_archive_module_in_owned_scope_v1` | `Result<MirModule,text>` | No direct production caller found by exact method-name search. Executable callers: `archive_borrowed_module_mechanics_spec.spl:99,133`, `archive_borrowed_module_lifetime_spec.spl:30,41,59`. Calls raw entry at :163 after archive/source authority checks and continuation symbol writes |

External raw-entry callers, all with actual MIR receivers:

| Call site | Target / error handling category |
|---|---|
| `src/compiler/50.mir/verification_call_lowering_v1.spl:70` | Explicitly unbound legacy verification branch. Uses unknown context; sibling explicit branch uses the new adapter. Both check capture errors and `lowering.errors` before finalizing receipts |
| `src/compiler/50.mir/enum_semantic_lowering_v1.spl:345` | `new_for_target(symbols,target)`; source-environment admission and `prepare_enum_semantic_declarations_v1` precede raw lowering; capture/diagnostic checks follow |
| `src/compiler/70.backend/backend/compiler.spl:50` | `new_for_target` with backend-derived context; maps lowerer diagnostics to `BackendError` before code generation |
| `src/app/simpleos_tool/focused_pipeline.spl:69` | `MirLowering.new(hir.symbols)`, hence legacy unknown context. Must explicitly resolve a request before strict migration; cannot silently grant portable authority |
| `src/compiler/70.backend/backend/native/remote_arm32_compile.spl:72` | Explicit `new_for_target` receiver. Recorded as another lane's migration dependency only; no ARM implementation audit/change |
| `src/compiler/70.backend/backend/native/remote_riscv32_compile.spl:43` | Explicit `new_for_target` receiver. Inventory-only dependency; RISC-V remains excluded from this work |

`ML:3757 -> lower_module_emit_all_v1`, then `ML:3811 -> lower_module_emit_fn_v1`, are internal emission helpers, not independently discovered production entrypoints. Their future private session parameter must be forwarded from the admitted kernel, not recreated from mutable context.

## Prescans happen before module entry

The driver creates bootstrap/direct/fallback sessions at DP:1086,1210,1749 using `collection_target`. Target admission solely inside the optional adapter cannot protect their earlier reads.

| Owner / method | Direct production callers found | Migration consequence |
|---|---|---|
| ML:1955 `prescan_module_struct_names` | DP:1106,1297,1315,1766; `backend/jit_interpreter.spl:200` | Reads module/symbol/type metadata and delegates to function prescan; admission must precede the first read/write |
| ML:2063 `prescan_module_functions_v1` | ML:2054 | Delegates each extracted signature to ML:2083 `prescan_one_function_v1` |
| ML:2122 `prescan_one_function_v1` | ML:2083; self-reference ML:2137 is the documented unreachable inliner shield | Preserve scalar call shapes and explicit arguments; do not remove shield as cleanup |
| ML:1412 `register_module_enum_inventory_v1` | DP:1352 | Shared-session enum metadata mutation, before module emission |
| ML:2368 `register_module_enum_bootstrap_inventory_v1` | DP:1132; `backend/jit_interpreter.spl:201` | Adds runtime IDs and builtin enum seeds; not replaceable with a weaker generic inventory |
| ML:1456 `register_module_composite_inventory_v1` | DP:1133,1373; `backend/jit_interpreter.spl:202` | Composite/layout metadata is prepared before target-dependent emission |
| `declaration_providers_v1.spl:420 prescan_module_declarations_v1` | No direct production caller found; `test/fixtures/compiler/archive_enum_declaration_prescan_repro.spl:82` calls it | Include compact-declaration admission in the same future session contract; do not claim the archive route is live merely because the method exists |

Internal body-type prescan begins at ML:3734 (`prescan_block_for_struct_types`); its block/statement/expression helpers at ML:4296,4309,4355 remain beneath the admitted module kernel. The JIT route above proceeds directly to `lower_function` at `backend/jit_interpreter.spl:203`, so protecting only module emission does **not** cover all MIR tasks. Nested function/lambda lowering is another later migration category, not an inventory-complete assertion here.

## First vertical slice: explicit verification, with explicit errors

1. Keep existing `verification_source_environment_v1` admission before packaging retained input. Target validation must not replace its source-symbol isolation or final call-manifest checks.
2. Extract one target-session admission owner using the complete canonical thirteen-field identity and the constructor binding already present in the draft. It must reject unresolved placeholders and retargeted sessions before trace/cfg/prescan state changes. It is target binding, not a semantic portability or deep-freeze proof.
3. Move the guard into the mandatory lowering kernel. The explicit verification path must not be able to call an unguarded `lower_module_guarded_v1` or raw module body. Prefer a private admitted-session input to that body, plus `Result<MirModule,text>` at the public failure boundary. A second opt-in adapter does not satisfy this step.
4. Propagate `Err` through the explicit producer's existing `?` chain. Return before capture-row hashing or manifest finalization. After successful entry, retain current capture and lowerer diagnostic checks: successful admission does not mean successful lowering.
5. Keep `lower_module_with_resolved_calls_v1`'s unknown-target behavior only as an explicitly named compatibility route during migration. Do not silently route it through strict admission or silently convert unknown into the host. Its existence means global strict migration remains incomplete.

This slice needs a reviewed API migration decision before source edits: changing raw `lower_module` to return Result affects every raw caller above. Bootstrap entry must unwrap/propagate before publishing MIR; enum and backend consumers must translate admission errors into their existing Result/error types. Transient wrappers must return admission errors before opening a scope, and preserve abort/promotion/publication cleanup for errors after acquisition. The borrowed wrapper must leave the caller's lease intact and admit before continuation symbol writes. Unit-returning prescans need Result propagation or an admitted private session parameter; silently recording an error and continuing metadata mutation is insufficient.

## Remaining migration and acceptance

Remaining categories: driver bootstrap/direct/fallback prescans and module routes; compact/archive declaration and lifetime paths; backend/JIT direct-function route; nested lowerers; focused-tool legacy construction; other-lane remote entry dependencies; executable callers and source-shape specs. Keep provider feeds, archive arguments and native-safe explicit call arities unchanged. Any retained new session handle requires transient owner promotion coverage.

Before claiming the explicit slice complete, execute rejection tests at the **actual** kernel and producer: mismatched input, unresolved context, and changed mutable session context must produce a named error with unchanged trace/scratch/capture state and no finalized receipt. Valid same-target reuse must preserve selected cfg arms, MIR/module hashes, call bindings and deterministic receipts. A compile-time misuse test must show the private admitted kernel cannot accept a raw module/session substitute. Legacy behavior must be tested separately and labelled compatibility. Broader rollout additionally requires transient/archive sabotage cases, prescan-before-lowering rejection, JIT/nested-context propagation, and real self-hosted/native Stage 3 evidence.

Deep immutable HIR ownership, frozen resolution payloads, semantic-read witnesses, region pins and removal of all raw-HIR bypasses remain separate unmet plan gates. This artifact closes the bounded caller/error-contract inventory prerequisite only; no implementation, test PASS, draft readiness, or release qualification is asserted.
