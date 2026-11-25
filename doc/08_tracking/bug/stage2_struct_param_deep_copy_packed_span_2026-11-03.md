# Frozen stage2 faults in the prologue deep copy of a by-value `HirExpr` parameter (packed `HirType.span` read as a pointer)

- **ID:** stage2_struct_param_deep_copy_packed_span_2026-11-03
- **Priority:** P1 (phase 3: every real module -- `app.test_runner_new.test_runner_main` 1/320, `app.cli.native_build_main`
  14/1486, `app.protocol.mcp_request_envelope` 3/156 -- dies in HIR lowering on the stage3 candidate; hello survives)
- **Status:** resolved (2026-11-25). Root cause was NOT a packed `Span` in MIR struct-copy codegen:
  `HirExpr.type_` is a non-optional `HirType` struct field (with `has_type_: bool` as the authoritative presence bit),
  and producers storing `nil` / `None` / `HirType?` (`Option<HirType>`) directly into `HirExpr.type_` placed an
  `RtCoreEnum` box (`word[1] = (discriminant << 32) | enum_id = 0x100000000`) where `HirType.span` lives. When any
  callee ran `copy_struct_value_recursive` (`src/compiler/50.mir/mir_lowering_stmts.spl`), the non-null/non-nil
  guard passed on the Option box and recursed into `0x100000000` as a `Span*`.
  Commits `87aaaa999c7`, `735ceebbfc6`, and `105a7883010` fixed almost all `HirExpr` producers (`type_: HirType(Unit, ...)`
  for untyped placeholders, bare unwrapped `HirType` for `retain_attributed_collection_type`, tuple destructuring, and
  positional `t.N`), and `switch_operators_calls.spl` (`option_record_receiver_payload_v1`) unwraps typed `T?` records
  into non-optional `T` fields. The final 3 remaining `type_: nil` / `type_: None` `HirExpr` producers
  (`expression_core.spl` range index, `declaration_enum_metadata_v1.spl` enum discriminant/field default, and
  `interpreter.spl` probe/fallback `HirExpr`s) were fixed and all 17 `@workaround` tags removed.

## Symptom
`native-build --entry-closure` on a stage3 candidate (s3_fable9b / s3_fable13) parses the closure, then the HIR worker dies
with rc=0xC0000005 on the first real module. VEH report (`C:/dev/p3new/f3/dumps/av_88088.txt`, s3_fable13):
`rip=image+0x6821ab = compiler.hir.hir_lowering.binding_types.hir_binding_direct_call_return+0x1ab, addr=0x100000000`.
The preceding `[simple-runtime][error] rejected invalid array handle before dereference` line is a separate, non-fatal
parse-phase bug (`rt_array_len` from `_FlatAstBridge.convert_nodes.convert_decl_fn`); it prints on hello too.

## Root cause (frozen stage2 codegen, reproduced on two object lineages)
`hir_binding_direct_call_return(source: HirExpr, symbols)` takes the expression by value. The frozen stage2 emits a deep copy
of that parameter in the callee prologue: it reads `source+0x10` (`type_: HirType`), treats it as an optional box
(`!= 0 && != 3`), then reads that object's word 1 (`HirType.span`) and treats it as a pointer to a 0x30-byte struct
(`movups (%rdx),%xmm6 ...`). The producer stores the span packed (`0x100000000` = line 1, col 0), so the copy
dereferences a non-pointer. The walk only happens when the `type_` placeholder stored with `has_type_ = false` is non-nil,
which hello never produces. The crash is identical on objects from the 10:30 combined3 run and on the fully rebuilt
hirfix2c lineage (all 965 objects fresh), so it is not a cross-object layout mismatch. The sibling call
`_hir_expr_symbol_or_invalid(source.kind)` on the same path survives, which is why passing the kind is the workaround.

## Workaround / fix direction
Pass `HirExprKind` instead of `HirExpr` (done, tagged `@workaround bug=stage2_struct_param_deep_copy_packed_span_2026-11-03`).
The real fix is in the stage2 codegen's struct-parameter copy: a nested struct field stored packed/inline must be copied as
such, not as a boxed pointer. Remove the workaround once a stage2 with that fix is frozen.
