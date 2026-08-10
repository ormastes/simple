# Stage 3 native context and named-type boundary failures

Date: 2026-08-10
Status: partially fixed; final owner-local named-type change not yet rebuilt

## Scope

A fresh canonical `--full-bootstrap` on current `origin/main` first rebuilt the
immutable Rust bootstrap authority, then produced a current-source Stage 2 and
entered the pure-Simple bare-positional Stage 3 lane. This cleared the prior
1,406-error stale-frontend alias/type cascade.

## Boundary 1: source-loading return

Stage 3 initially trapped with `field access on nil receiver` in
`CompileContext.has_errors`, called by `CompilerDriver.load_sources_impl` while
forming its `(loaded_ctx, bool)` return. LLDB showed the copied local context as
the bad receiver. The phase now derives success from the stable owner scalar
`self.ctx.error_count_value == 0`. A rebuilt Stage 2 passed this boundary and
continued into HIR lowering.

## Boundary 2: named method-self type

The next run faulted in `_hir_named_type_symbol` while transporting
`SymbolId?`. Changing only the return to raw `i64` did not fix it: the third
bounded run faulted at the same instruction shape in
`_hir_named_type_symbol_raw`, proving the unsafe value is the `HirType`
argument crossing the helper boundary, not merely the optional result.

The final scoped source change removes the helper and matches
`self_type.kind` directly inside `field_type_for_base_raw`, returning only the
raw symbol ID locally. It has source-contract coverage but was not rebuilt:
the mandatory three verify/fix cycles for this session were exhausted.

## Evidence

- Output: `build/qemu-port-bootstrap-current`
- Stage 3 log:
  `build/qemu-port-bootstrap-current/logs/aarch64-apple-darwin/stage3-native-build.log`
- First LLDB stop: `CompileContext.has_errors + 40`, caller
  `load_sources_impl + 8696`.
- Final LLDB stop: `_hir_named_type_symbol_raw + 176`, caller
  `field_type_for_base_raw + 860`, then HIR expression/statement/function
  lowering.

No Stage 3 artifact was admitted or deployed. No Rust seed was substituted for
the requested pure-Simple compiler.

