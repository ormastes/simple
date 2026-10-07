# Flat parser encodes an absent Range bound as a present negative literal

Status: owner repair integrated; focused native open/bounded-range execution passed on both LLVM and Cranelift. Full phase qualification remains pending.

Actual producer SHAcd000950b565769d8261d03d0fe822c712e28212bf67d8dc6d3c31bb19da0327 (LLVM Phase2 built from a32 source) links open_range_break, whose output is0 instead of6. Bounded_range_sum prints6. All three sanity compile commands including Hello also fail at process exit with SIG139 in LLVM PassRegistry destruction; that separate cleanup failure must remain visible.

Pure `core/parser_expr.spl` parse_range used `expr_range(left, expr_int_lit(-1,0),...)` for a missing end. That creates a real endpoint expression. The flat-to-tree bridge correctly treats its nonnegative node ID as present, HIR carries Some(IntLit(-1)), and MIR consequently tests the positive counter against -1. The existing absent-end MIR Goto repair cannot apply to this present endpoint.

Direct parser/bridge diagnostic proves `(1..)` generated Range node2, left0, right1, right tag1, right value-1, converted tree end-present=true. The repair uses absent node ID-1 instead, preserving an authored actual negative bound as a distinct present expression. Named call-argument continuation parsing applies the same endpoint rule. Body colon and semicolon are valid terminating delimiters.

Actual Phase1 regressions: baseline original cases2PASS/1FAIL; selected failing case repaired1PASS; new colon and continuation cases2PASS. Existing green cases were not repeated.

Combined source `16831ca691ec5f31962975bfa5c0912083046ced` produced strict no-stub LLVM compiler `d81e3254c06d0ac7f6323063e4ffafce4f6b24dda0b9286492635fdf076a929d` and Cranelift compiler `e3d9bb4bbeddfa5315b898b01d21e8948f8ebef3605e5e6818fb985f3bdea0ce`. Each compiled and ran Hello, `test/fixtures/bootstrap/open_range_break.spl` and `bounded_range_sum.spl`: expected outputs Hello, 6 and 6, exit zero, empty execution stderr. Each sanity directory retains compile/run watchdog receipts and exact output comparisons under `/tmp/simple-linux-combined-phase2-{llvm,cranelift}-20261006/sanity/`. These direct-route diagnostics bypassed the coordinator and do not admit whole Phase 2 or normal cold publication. The original failed cleanup and range receipts remain historical evidence rather than overwritten results.

Remaining legacy parity: core/compiler/cg_stmt.spl90 and core/interpreter/eval_stmts.spl422 still assume a present Range end; standalone eval_range also materializes finite arrays. Those legacy paths already mishandled open-ended ranges before this repair and need explicit iteration/representation handling in their own tests. They are not proof against the LLVM parser owner fix, nor silently marked solved.
