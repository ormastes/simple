# Daemon host generic inference rejects contextual callbacks and a projected local

Status: source repairs and regressions passed independent static review; runtime validation pending.

The native daemon-host build from source `2f55ac2a6d67b2797633c51d9a94db00dc7a9f36`, using admitted compiler17 SHA256 `9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`, completed HIR but failed monomorphization with five unresolved calls. The build produced no daemon executable. Its source/runtime/tool checks passed; this is not a daemon qualification result.

Retained evidence: `/tmp/simple-generic-daemon-host17-build3-20261030/build.log` and `cache/diagnostics/native-build-stderr-1729850-1.log` beneath that output directory. The aggregate E-MONO-033 diagnostic repeats; it does not represent additional sites.

## Failing sites

| Source at the failed revision | Call | Missing evidence |
| --- | --- | --- |
| `src/compiler/90.tools/header_gen/mod.spl:113` | `array_sort_by` | Comparator lambda, argument 1 |
| `src/compiler/90.tools/header_gen/mod.spl:117` | `array_sort_by` | Comparator lambda, argument 1 |
| `src/compiler/90.tools/header_gen/cpp_header.spl:428` | `array_sort_by` | Comparator lambda, argument 1 |
| `src/compiler/90.tools/header_gen/c_header.spl:338` | `array_sort_by` | Comparator lambda, argument 1 |
| `src/compiler/99.loader/module_loader_compat.spl:1621` | `global_symbols_without_names` | Projected local symbol 728, argument 0 |

## Confirmed callback defect

`infer_call_bindings_signature_v1` learns bindings from an earlier concrete array argument, but immediately refuses an untyped lambda against the original generic function parameter. It does not first instantiate the callback expectation using those bindings. Expected-result constraints are processed only after that refusal.

Simply ignoring missing evidence is unsafe: callback arity, parameter types, return type and nominal identities must agree, and contextual parameter types must survive into the rewritten lambda so native lowering uses the intended ABI. Unknown non-lambda expressions must remain rejected.

## Confirmed tuple-projection gap

Retained parser-HIR record `07015b1c45e3c1ab933fbcd40b96d5f34ec051b51bdbe317f4a9e784336309a5.parser-v4.hir` stores temporary symbol 726 and projected local symbol 728 as `Infer(0,0)` (codec tag 21 denotes Infer). Generic functions are excluded from the frontend tuple-return registry, so tuple destructuring emits `Index(temp, IntLit(1))` without a concrete annotation.

Mono inference can recover instantiated generic-call results and separately supports the `TupleIndex` expression. However, the actual `Index` branch supports arrays, slices and dictionaries only. It therefore cannot recover the projected local even when the temporary has a concrete tuple type. The repair must accept only literal, in-bounds tuple indices with concrete element evidence, preserving nominal identity and rejection of dynamic or invalid projections.

The retained diagnostic does not itself prove the runtime mono environment successfully recovered temporary 726. A chained generic partition/destructure/filter regression must verify the complete path rather than testing the projection helper alone.

## Regression requirements

Positive cases must exercise inferred callbacks for concrete record arrays, later argument witnesses and expected-result constraints, and preserve deterministic ordering. Negative cases must reject wrong callback arity, incompatible explicit parameters, incorrect return types, conflicting generic prefixes, foreign same-name nominal types and genuinely missing non-lambda evidence. Tests must also show contextual environments do not leak between calls.

The loader regression must carry the concrete partition-result element through tuple projection into the filtering call, preserve owner identity, and reject incompatible projected/result types.

## Validation boundary

The original compiler17 SSpec positive and authenticated assertion-negative tests passed separately. The broad verification matrix was stopped for disk pressure, and default daemon execution remains unqualified. No success in this report substitutes for executing a daemon built with the eventual repair.

The tuple-projection regression is `test/01_unit/compiler/mono/tuple_index_inference_spec.spl`. It invokes the production inference owner directly and also runs parsing, HIR lowering, monomorphization and post-mono verification on the chained generic calls. Static review passed; no execution result is claimed yet.

Callback source-owner coverage is in `test/01_unit/compiler/monomorphize/contextual_callback_inference_spec.spl`. Standalone fixtures `contextual_callback_native.spl` and `contextual_callback_invalid_return.spl` in its `fixtures/` directory exercise real native callback/tuple behavior and rejection of a Bool-returning callback where i64 is required. These fixtures are authored; execution remains pending.

Before sealing the candidate, working and staged direct-env runtime guards passed, and the executable-spec count under `doc/06_spec` was zero. These static checks do not imply runtime qualification.

## Native validation exposed missing receiver metadata

Compiler18 built from candidate `5a11bcaf1f17cecdd0a032d80d823ab3fdf9ff36` successfully compiled and linked `contextual_callback_native.spl`, but its executable failed the second assertion, the direct `.value` comparator expecting 57. The typed-local name comparator before it passed. The negative callback fixture rejected the incompatible return as intended; the separate typed-key and optional-tuple fixtures passed.

LLDB stopped at `rt_panic` with caller `__simple_main + 648` in binary SHA256 `f838e4da2c7bad1f7bef04643aaa8cd326d4a2027920713627bd1458a86e51e9`. Disassembly of `__lambda_lift_1` at file address `0x1536c` showed both `.value` reads loading offset zero, although `CallbackRecord.value` is at offset eight. It subtracted the name pointers. Retained evidence is `/tmp/simple-callback18-lldb-diagnostic-20261030/`; the partition assertions were not reached.

Contextual parameter declarations and the mono environment were concrete, but ordinary variable-reference HIR retained unresolved types. MIR field selection depends on the receiver type/provenance, so annotating only the lambda parameter was insufficient. The follow-up persists concrete environment types on unresolved Var/NamedVar reads in the existing expression rewrite, and transports inferred ordinary field types from their declaring module before annotating nested reads. Existing concrete annotations remain authoritative. No second expression traversal or field-offset fallback is added.

The source regressions now inspect rewritten receiver and field metadata, including nested cross-module nominal identities. The standalone fixture retains the original failing assertion and adds nested member reads at two nonzero offsets. The follow-up requires a new source-matched producer and actual native execution; static review alone does not resolve this runtime failure. Existing compiler18 artifacts and its failed original fixture remain unchanged.

## Producer19 reaches the final tuple member assertion

Compiler19 from `a8006bd4334eeb67c993bb1932087c40ddd6daf0` fixes the original callback offset failure. LLDB confirms both direct callback `.value` loads now use offset eight; the original, nested callback and partition/filter assertions execute successfully. The fixture then fails its final `retained[1].value == 42` assertion. The negative callback, typed-key and optional-tuple rows passed separately.

The retained binary SHA256 is `9b22bf16843700d25197d83fb36d489ff1a3281fa20b7354ff9d602e58eec916`. LLDB reports `rt_panic` from `__simple_main + 6040` (file return address `0x17060`). Disassembly loads tuple slot one at offset eight, then incorrectly loads the record member at offset zero. Evidence is retained at `/tmp/simple-callback19-lldb-diagnostic-20261030/`.

Projection inference already knows the concrete result type, but the Index and TupleIndex rewrites did not retain it. The next narrow change persists an inferred concrete projection type through those existing rewrite branches, preserves existing concrete annotations and generic-instance correction, and leaves invalid or unknown projections unresolved. Source tests cover tuple, array, slice and dictionary member receivers, caller-owned nominal identity, valid dynamic array/slice indices and invalid selectors. The native fixture retains the original final assertion and adds sibling array/dictionary member checks. A new producer must validate the complete chain before this report can mark runtime correctness resolved.
