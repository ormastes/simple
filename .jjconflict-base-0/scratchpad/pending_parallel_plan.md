# Parallel-Agent Plan — All Pending Tasks (2026-07-13)

## Hard constraints that forbid naive "all-at-once"
1. **File conflicts.** Agents editing the SAME `.spl` file in parallel produce merge hell.
   Lanes MUST own disjoint files. The hot shared file is
   `50.mir/_MirLoweringExpr/method_calls_literals.spl` (methods, literals, many bugs).
2. **Redeploy-gated (can't take effect now).** Rust-seed changes need a seed rebuild,
   owned by the parallel `bootstrap-from-scratch` loop → these go to a REDEPLOY QUEUE,
   not a live lane: #112, #152, #153, #159, #99.
3. **Oracle caveat.** The interpreter oracle is itself WRONG for some features
   (#162 match guards, #168 operator dispatch SIGSEGV) → native fixes for those can't be
   oracle-verified until the interpreter is fixed. Also OPEN: is `bin/simple run` the Rust
   seed's interpreter (redeploy-gated) or the interpreted `.spl` interpreter (live)? Lane F
   must determine this first.
4. **Verify gate (all lanes).** native == interpreter oracle on the ACTUAL origin tip +
   full `native-smoke-matrix.shs` >= 14/15, 0 new fail, 0 fallback. No "rc=0" trust.
5. **Disk discipline.** Each agent removes its worktree on completion (1038 stale worktrees
   already crashed the box once).

## Root-cause grouping (many "bugs" are facets of few keystones)
- **Method resolution keystone** (native --entry resolves NO instance methods): #156, #157, #161.
- **Closures keystone** (Lambda unimplemented): #165, and #155 (map/filter/fold needs it).
- **Generics keystone** (unimplemented): #158.
- **Match/pattern lowering**: #164 (nested vars), #163 (loop-expr break value), part of #169 (tuple/Some-None).
- **Loop/SSA**: #160 (break-SSA).
- **Struct codegen**: #166 (nested field offset), #167 (by-value→ref).
- **Interpreter correctness**: #162 (match guards), #168 (operator SIGSEGV).
- **Dict/enum lowering**: part of #169 (enum-in-Dict llc type).

## Lanes (disjoint file ownership → safe to run in parallel)
| Lane | Tasks | Owns (files) | Status |
|------|-------|--------------|--------|
| A. Match/pattern | #164, then #163 | 50.mir match/pattern lowering | #164 RUNNING |
| B. Loop/SSA | #160 | 60.mir_opt/var_reassign_ssa + loop stmt | RUNNING |
| C. Struct field codegen | #166 | 70.backend field GEP/offset | LAUNCH |
| D. Native value semantics | #167 | 50.mir param bind (arg_binding/function_exec) | LAUNCH |
| E. Method-resolution keystone | #156+#157+#161 | HIR resolve + method_calls_literals + parser self | QUEUE (big, serialize; owns the hot file) |
| F. Interpreter correctness | #162, #168-interp | 10.frontend interpreter (determine seed-vs-spl first) | QUEUE (needs seed/spl determination) |
| G. Build-fail cluster | #169 (enum-in-Dict, Some/None) | dict lowering + name resolution (NOT tuple — that's Lane A) | QUEUE (after A frees pattern files) |
| H. Feature keystones | #165 closures, #158 generics, #155 | multi-stage (parser→HIR→MIR→backend) | PLAN-ONLY (large features; scope before impl) |

## Redeploy queue (hand to the bootstrap loop / do after next seed deploy)
#112 (class-in-array, banked /tmp/arrmut.patch), #152 (rt_get_args alias), #153 (compiler_driver_create),
#159 (rt_cli_arg_count test runner), #99 (stage4 HIR completeness). Interpreter fixes (#162/#168) land in
`.spl` but only deploy via the seed if `bin/simple run` uses the Rust interp — Lane F resolves.

## Execution order
1. NOW (parallel, disjoint): Lanes A, B, C, D + ongoing discovery sweeps.
2. After #164 done → Lane A takes #163; then Lane G (pattern files free).
3. Serial (owns hot file): Lane E method-resolution keystone — biggest #138 unblock, one focused effort.
4. Lane F once seed-vs-spl is determined.
5. Lane H (closures/generics) — scope → plan → implement as features, not bug-patches.
6. Redeploy queue → next verified seed deploy.

## Note
This is DISCOVERY-heavy: the native single-file self-host path (#138) is missing whole
feature areas (methods, closures, generics, operators, tuples). Full #138 self-host is a
feature-implementation program, not a bug-fix sprint. Fixable-now bugs: #160, #164, #166,
#167, #163, #161, parts of #169. The rest are features or redeploy-gated.
