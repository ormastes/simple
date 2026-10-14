# Item 5: open Phase 3 failures (2026-10-14)

Status: OPEN. The user authorized landing focused fixes with these bugs recorded, then manual object repairs and follow-up landings. This is not full Item 5 completion, a Phase 3 PASS, or release admission.

Source b061b531beb565aed991ce1817fc7877bb2e25d9; producer a713c24f7049ed0e3fb05bf25c6fa61224a785502d5408b081f20bbf9bbe6915; runtime archive 6e803d2401ba8d1283e32f99232ef866d33e228b2996a5fbda76a961d4faea32. The producer compiled and executed Hello. Its Phase 3 descendant has not.

## item5_phase3_early_mir_crash_2026_10_14

P1: Phase3 compiler crashes in early MIR after zero unresolved generic calls.

Frozen b061/a713 canonical381 closure exited139 after635.226s. HIR381 completed; Mono65 functions430 calls124 specializations and zero unresolved. MIR0/381 then crash; no objects. Memory reserve remained above21GiB. Corrected GDB captured SIGSEGV at PC0xb90168 in MirLowering.relocate_provider_type+244, called by relocate_provider_default then register_provider_class. The invalid provider-type operand cause remains under repair; the CompileError warning is not established as causal.

Owner/source: `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md`.

## item5_generic_optional_payload_acceptance_2026_10_14

P1: Generic specialization accepts wrong optional enum payload.

Actual wrap_unknown<text> specialization compiled an UnknownEnvelope.Value(Some(value)) for declared i64? payload. Reachable ELF specialization verified; no negative execution or passing rejection claimed. Exact post-substitution validation boundary remains unresolved. Primitive positives and wrong-inner/Any rejection results do not qualify this generic case.

Owner/source: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`.

## item5_cranelift_module_data_support_2026_10_14

P2: Cranelift cannot declare imported globals or non-scalar module statics.

Actual AOT rejects imported globals and signal handler non-scalar initialization. Guards remain intact. LLVM object generation passes for signal_stubs, trace_policy, AST nodes and process_ops. Mixed LLVM/Cranelift linkage and runtime initialization are not qualified.

Owner/source: `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`.

## item5_native_object_resource_growth_2026_10_14

P1: Native object collection exceeds diagnostic memory reserve.

SymbolTable87 passed MIR then exited143 at shared4GiB RAM-plus-swap reserve;69 private LLVM objects retained. Aggregate process RSS exceeded28GiB in some successful cohorts; shared-memory contribution is unisolated. No memory-leak cause or performance qualification claimed. Owned temporary swap is diagnostic only.

Owner/source: `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md`.

## item5_native_build_threads_ineffective_2026_10_14

P2: Native builder thread option does not parallelize module compilation.

Actual pure-Simple native builder reports thread counts above one have no effect; module generation remains sequential. Separate diagnostic object jobs and parallel repair agents do not prove internal backend parallelism. Parallel implementation and qualification remain pending.

Owner/source: `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md`.

## item5_backend_error_opaque_enum_2026_10_14

P2: Backend AOT diagnostics discard structured error details.

Retained AOT message renders CompileFailed as opaque enum address. Actual backend messages identify missing static-data support. Private36945ca diagnostic patch retains typed CompileError fields and explicit authority variants; patch is unbuilt and unlanded.

Owner/source: `src/compiler/70.backend/backend_plugin/session_authority_v2.spl`.

## explicit_generic_interpolation_transport_2026_10_14

P1: Canonical interpolation loses explicit helper type arguments.

Canonical six profile calls lost flat/rich/HIR type arguments before the rich bridge. Computing typed helper vals inside the same receipt branch preserves all six argument arrays and clears canonical monomorphization. Underlying interpolation owner remains unresolved; workaround is not a parser repair.

Owner/source: `doc/08_tracking/bug/explicit_generic_interpolation_transport_2026_10_14.md`.

## bare_enum_pattern_binding_in_compiler_2026_10_14

P1: Contested bare Function enum pattern becomes a binding.

Actual SymbolTable.is_function HIR lowered bare Function to Binding and wildcard, causing B5b. Qualified SymbolKind.Function workaround clears B5b and reaches backend generation. General contested bare enum resolution remains open.

Owner/source: `doc/08_tracking/bug/bare_enum_pattern_binding_in_compiler_2026_10_14.md`.

## Evidence and next steps

Retained receipts are under build/review: item5-functionfield-cache-resume-object-20261014, item5-functionfield-mir-crash-parent-gdb-20261014, item5-four-failed-llvm-collection-20261014.md, and item5-parallel-blockid-object-b061-20261014/object-aot-inventory.json. All objects stay bound to their own closure, producer, runtime and backend. Preserve failed receipts; use exact required object sets for manual links.

Fix the observed MIR crash owner, qualify each changed object, build the full compiler, and execute Hello using that compiler. Native Simple DB/HTTP scalar-versus-AVX512 correctness/performance, CUDA and other provider/device qualification, small-executable targets, and full tooling/CI acceptance remain outstanding. Restore normal admission gates before promotion or publication.
