# LLVM MIR bitcast pointer/integer legalization

Status: source repair, native qualification pending. Base source 2388ee1959fd31756ef1118cff258b9dd0be0507. No compiler build or execution was run in this repair lane.

## Actual failure

The retained LLVM optional-trait and struct-trait builds failed in llc with `bitcast i64 %l6 to ptr`. Both load the integer runtime ABI result from `rt_enum_payload`, then reinterpret the payload as a pointer. Evidence root `/mnt/item5-release-20261009/regressions-2388-t86bpvw7`:

- `llvm-trait-optional/cache/s233746a32dedcfec660359fed1416e58/simple-aot-diagnostic-y5pX1Y/message.module.ll`, lines104?105.
- `llvm-trait-struct/cache/sacaa3e7389b8854e1ccb02a841e12076/simple-aot-diagnostic-EWpjR2/message.module.ll`, lines109?110.

## Owner and correction

`aggregate_intrinsics.spl::llvm_bitcast_impl`, selected by the canonical MIR Bitcast instruction dispatch, previously emitted LLVM bitcast for all differing types. Integer/pointer conversions require inttoptr or ptrtoint. Add those two branches, including i1, without changing source metadata, runtime signatures, pointer tagging, same-type identity, or floating-point bit reinterpretation. A pointer-to-i1 Bitcast preserves the low bit as specified by ptrtoint; numeric/boolean Cast coercions keep their existing non-null semantics.

The existing `llvm_bitcast_pointer_bool_spec.spl` exercised return coercion rather than this owner. Five additional scenarios call the actual MIR bitcast owner and assert integer/pointer conversion in both directions, same-pointer identity, integer/float bit reinterpretation, and one-bit conversions. These new scenarios have not been executed.

## Required qualification

Run the focused backend spec under a compiler capable of executing it. Under the next rebuilt qualified compiler, rebuild and execute the unchanged `test/04_smoke/native_trait_optional_owner.spl` and `test/04_smoke/native_trait_struct_copy_borrow.spl` with LLVM. Preserve independent failures if either encounters another boundary. Cranelift and full application qualification are separate; this patch changes only the pure-Simple LLVM emitter. Source review/diff checks are not native PASS evidence.
