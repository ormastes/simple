# C1 compiler-owned resolved call transport

Source: `test/01_unit/compiler/mir/verification_call_lowering_v1_spec.spl`.
Requirement: selected Verification 2.0 C1 typed VIR/call-identity transport (`REQ-FV2-C1`).
Audience: compiler and formal-verification maintainers.

This manual describes 20 authored SSpec scenarios. **Every scenario is UNRUN.** No compiler, test runner, native build, Lean checker, replay tool, or proof gate was executed for this source packet. The initial positive spec was saved before the new producer owner existed; this is tests-first source evidence, not an observed runtime RED or PASS.

## Actual execution path under specification

`parse_full_frontend` → fresh `HirLowering.with_filename` → `HirLowering.lower_module` → `lower_module_with_resolved_calls_v1` → the existing manifest validator and site lookup. The zero-argument scenario also calls `verification_ir_module_from_hir_calls_v1` and checks the resulting resolved VIR's closure flag and function inventory. Helpers require a clean HIR diagnostic list, inspect actual emitted MIR instructions, and compare scalar fields or canonical signature serialization. They do not create resolver captures, manifests, receipt flags, or synthetic MIR positives.

`c1_calls_function` matches the exact `c1_calls.<name>` spelling for ordinary declarations in the fixed `c1_calls.spl` fixture. This follows `mir_provider_function_name_fields_v1` → `mir_provider_callable_identity` in `provider_metadata.spl`: no extern/export/entry attribute applies, and the normalized module owner prefixes the source name. No bare-name or suffix fallback is accepted. Call operands are compared to that exact located definition name.

`c1_calls_check_site` finds the actual owner and callee, inspects emitted argument count and exact ordered declaration signature, recomputes the final instruction-site identity, and requires one matching binding with the real owner/callee SymbolIds and final callee signature/body hashes. It calls the existing validated lookup for that exact site. The nested-call scenario requires distinct sites; the default-argument scenario checks the final filled argument count and site after ordinary lowering. The default-call scenario also snapshots source symbol/scope allocation counters and symbol/scope/root-map key counts, requiring all to remain unchanged after the producer returns. These are transport assertions, not execution of the call's arithmetic result.

## Scenarios

| ID | Executable scenario | Evidence |
|---|---|---|
| C1-CALL-01 | captures an actual zero-argument declaration and admits its resolved VIR | UNRUN |
| C1-CALL-02 | retains a one-argument declaration signature rather than an unknown parameter list | UNRUN |
| C1-CALL-03 | preserves ordered heterogeneous parameters for a multi-argument direct call | UNRUN |
| C1-CALL-04 | captures nested calls at their final distinct instruction positions | UNRUN |
| C1-CALL-05 | captures the call after materializing its omitted trailing default | UNRUN |
| C1-CALL-06 | rejects final MIR body and signature mutations against the original produced manifest | UNRUN |
| C1-CALL-07 | refuses a foreign declaration instead of fabricating a local resolver capture | UNRUN |
| C1-CALL-08 | refuses an actual function-parameter indirect call | UNRUN |
| C1-CALL-09 | refuses an open generic template before publishing resolved MIR | UNRUN |
| C1-CALL-10 | refuses HIR owner and parameter-signature mismatches | UNRUN |
| C1-CALL-11 | keeps empty and pure call-free modules valid with zero capture rows | UNRUN |
| C1-CALL-12 | isolates sequential producer owners even when source function names repeat | UNRUN |
| C1-CALL-13 | copies mutable symbol rows and root maps without aliasing the source environment | UNRUN |
| C1-CALL-14 | binds distinct explicit targets into the resolver receipt for the same typed source | UNRUN |
| C1-CALL-15 | captures a same-module call inside an omitted default before its consuming call | UNRUN |
| C1-CALL-16 | keeps same-path same-name defaults invocation-local across an intervening failure | UNRUN |
| C1-CALL-17 | ignores a stale process-global default installed through the real MIR prescan | UNRUN |
| C1-CALL-18 | preserves the serialized HIR and complete symbol table on default success and failure | UNRUN |
| C1-CALL-19 | binds an omitted default to the earlier supplied parameter in the same invocation | UNRUN |
| C1-CALL-20 | refuses an active omitted-default expansion cycle while retaining ordinary recursive calls | UNRUN |

## Mutation and boundary controls

The body and signature controls mutate fresh completed MIR while retaining its original compiler-produced manifest. The existing validator must reject the module snapshot hash; the tests do not regenerate the manifest or replace hashes to conceal a mutation. The HIR controls retain the frontend-created symbol table while changing either a function's SymbolId against its map key or an ordered parameter type against its declaration signature. A separate heterogeneous `(bool, i64)` mutation swaps the ordered parameter types without changing their count or set; this must also be rejected.

The signature control follows actual declaration publication: `module_declarations_bootstrap.spl` computes `declared_callable_type` and publishes it with `symbols.define`; `module_callable_types.spl` constructs a Function from ordered annotated parameters and explicit return type. All positive fixtures use explicit annotations. Open templates, foreign calls, and indirect function-parameter calls must return a nonempty error. The foreign fixture first calls a valid retained local declaration, then calls the foreign declaration in the same body. This requires atomic refusal of the module/manifest result after an earlier valid capture; no partial success is accepted. Empty and pure modules must have no capture rows. Sequential same-name productions must remain isolated, and a manifest from one module must fail against another module's snapshot.

## Source environment and explicit target controls

The environment-isolation scenario uses the real public `verification_source_environment_v1` API on a frontend-created SymbolTable. It changes a copied HirSymbol row's name and inserts distinct keys through each copied root-map view. The original symbol name, source maps, key counts, and allocation counters must stay unchanged. The copied `root_scope_symbols` and `scopes[0].symbols` must observe each other's insertions, preserving the intended alias only inside the new environment. This exercises mutable row/map separation; immutable type/span values remain borrowed. It does not claim a deep AST copy or test every secondary index.

The target scenario calls `lower_module_with_resolved_calls_for_target_v1` twice on the same explicitly typed HIR, with `mir_target_context_from` for `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`. Both produced manifests must pass the existing validator and site checks; their derived resolver receipt hashes must differ. These are source target-binding assertions, not native execution, target qualification, or authenticated receipt evidence.

## Cycle 2 retained default-expression regression evidence

Six added scenarios address C1-01 without replacing the original 14. The omitted-call default uses actual `seed()` HIR and requires two distinct compiler-produced bindings; the consuming call's second operand must use the result of the earlier emitted default call. Exact declaration-signature checks preserve its Bool/I64 argument order. `c1_calls_arg_literal` traces an actual integer argument through bounded MIR Copy/Move definitions to its Const, rejecting absent or nonliteral definitions.

Sequential productions use the same source path and function names with defaults 23 and 47, separated by a failed foreign-call default. The earlier result must retain 23 after the later invocation succeeds. A distinct warm-global scenario invokes the actual `MirLowering.prescan_one_function_v1`, verifies that `bootstrap_fn_param_defaults_lookup` holds its old literal 83, then requires the fresh verified invocation to use its retained literal 97. No registry emulator or caller-created MIR/capture is used.

`c1_calls_input_snapshot` uses the existing noncanonical `hir_module_encode`, explicitly requiring nonempty output. The generated encoder includes the HIR and SymbolTable rows, scopes, counters and secondary indexes. Byte equality before/after successful and failing expansion is a test-only mutation oracle; it does not authenticate source or substitute for canonical admission. The earlier-parameter fixture deliberately shadows the parameter's name in the caller with 99, while both actual call operands must resolve to the supplied 41.

The cycle scenario combines related controls: a two-function omitted-default cycle must refuse; an ordinary fully supplied recursive call must remain valid; and the same function may be re-entered while expanding a different default index (`a = f(1)`, `b = 2`). Real generated source declarations `depth_0` through `depth_128` test the frame bound: calling `depth_127()` admits 128 active default expansions and 128 call bindings, while `depth_128()` must return `DEFAULT-DEPTH`. Input snapshots must remain equal on both boundaries. These are authored assertions only; parser, lowering, depth, and codec execution remain UNRUN.

The cycle-2 tests-first snapshot is retained separately under `revision2-tests-first`; earlier snapshots and source receipts are preserved. The separate CLI suite is outside this helper's ownership and is unchanged by these edits.

## Authority and remaining scope

These tests do not authenticate caller-supplied provenance hashes or establish trusted producer admission. Cross-module relocation, general method/indirect/foreign call closure, monomorphizer integration, physical ABI refinement, authenticated checker/replay, and the remainder of C1/C2/C6/C7 remain open. A source review cannot replace the qualified execution and independent formal evidence required by the full ledger. No performance, native runtime, proof-completion, or blanket formal-GO claim is made.
