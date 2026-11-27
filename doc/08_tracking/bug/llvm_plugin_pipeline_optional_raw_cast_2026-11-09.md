# LLVM plugin PipelineOp raw optional destination fails strict bootstrap lowering

Status: source fix implemented; focused current-producer regression execution
and a new Stage2 build remain pending. No self-hosted qualification is claimed.

Build Binaries run42551927286 and Phase Ladder run42551927129, source c72e2c57,
failed Linux and MinGW Stage2 at
`src/plugins/backend_llvm_lib/llvm_lib_translate_expr.spl`. HIR reports
`SIMPLE_JIT_STRICT: cannot cast an optional T? to i64 with as outside unsafe`
(ERR01). The failing source remains present at release576f847f83c.

The PipelineOp arm constructs `dest_opt: LocalId? = Some(dest)` and hands its
raw tagged word to `translate_call`. Its `dest_opt as i64` occurred in safe
code. The callee tests the Some discriminant before projecting the destination;
replacing this cast with `?? 0` would erase the Option tag and mishandle Some(0).

The repair binds the raw word in a value-bound `unsafe(capabilities: [ffi])`
expression containing only that cast. The call consumes the resulting integer.
The Option construction and callee decoding remain unchanged.

Rust HIR regression
`llvm_pipeline_optional_destination_keeps_narrow_unsafe_boundary` extracts the
actual production unsafe binding. It checks strict lowering accepts that block,
retains its i64 result and single-statement ffi boundary, rejects the original
safe cast, and rejects a second optional cast after the boundary. It also checks
the production call consumes the raw binding. The local retained Nov7 compiler
authorities predate the Nov9 strict rule and cannot prove these outcomes; the
new regression is not reported as executed under those older producers.

Before evidence: `D:/dev/wt/lint-audit-evidence-20261109/release-build-nov9.log`
lines1723 and3438. Successful validation requires the current Rust HIR test and
the previously failing plugin file to compile in the actual Stage2 boundary.
