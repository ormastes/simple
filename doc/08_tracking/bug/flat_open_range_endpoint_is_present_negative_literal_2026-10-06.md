# Flat parser encodes an absent Range bound as a present negative literal

Status: owner repair prepared; self-hosted native integration pending.

Actual producer SHAcd000950b565769d8261d03d0fe822c712e28212bf67d8dc6d3c31bb19da0327 (LLVM Phase2 built from a32 source) links open_range_break, whose output is0 instead of6. Bounded_range_sum prints6. All three sanity compile commands including Hello also fail at process exit with SIG139 in LLVM PassRegistry destruction; that separate cleanup failure must remain visible.

Pure `core/parser_expr.spl` parse_range used `expr_range(left, expr_int_lit(-1,0),...)` for a missing end. That creates a real endpoint expression. The flat-to-tree bridge correctly treats its nonnegative node ID as present, HIR carries Some(IntLit(-1)), and MIR consequently tests the positive counter against -1. The existing absent-end MIR Goto repair cannot apply to this present endpoint.

Direct parser/bridge diagnostic proves `(1..)` generated Range node2, left0, right1, right tag1, right value-1, converted tree end-present=true. The repair uses absent node ID-1 instead, preserving an authored actual negative bound as a distinct present expression. Named call-argument continuation parsing applies the same endpoint rule. Body colon and semicolon are valid terminating delimiters.

Actual Phase1 regressions: baseline original cases2PASS/1FAIL; selected failing case repaired1PASS; new colon and continuation cases2PASS. Existing green cases were not repeated. No native PASS is claimed yet.

Remaining legacy parity: core/compiler/cg_stmt.spl90 and core/interpreter/eval_stmts.spl422 still assume a present Range end; standalone eval_range also materializes finite arrays. Those legacy paths already mishandled open-ended ranges before this repair and need explicit iteration/representation handling in their own tests. They are not proof against the LLVM parser owner fix, nor silently marked solved.
