# stage1 HIR fatals on lexer.spl: `unresolved name: eprint` and a `<T>` array-len helper

**Status:** FIXED (eprint, three `<T>` len helpers); OPEN follow-up (generated `hir_visitor.spl` walkers)
**Filed:** 2026-08-22
**Relates to:** #158 Phase B; `hir_generic_templates_unconsumed_by_mono_pass_2026-08-21.md`

## Summary

A stage1 build (tree `ab2cd110095`, lane fp9) fataled in HIR lowering of
`src/compiler/10.frontend/core/lexer.spl` with:

1. `unresolved name: eprint`
2. `generic functions are not supported on the native build path yet: fn
   'lexer_array_len' declares type parameter(s); monomorphization is not
   implemented (#158 Phase B)`

Both share ONE root cause: an exemption that only exists when the process has
`SIMPLE_BOOTSTRAP=1` in its environment.

- `eprint` was listed only in `is_bootstrap_builtin_fn`
  (`20.hir/hir_lowering/_Expressions/expression_support.spl`), which is
  consulted behind `hir_expr_env_get("SIMPLE_BOOTSTRAP") == "1"`, while
  `print`/`println` are in the unconditional `is_interp_builtin_fn`.
- `lexer_array_len`, `rt_array_len_safe` (lexer_struct.spl) and
  `decl_nodes_array_len` (_Ast/decl_nodes.spl) sat on a three-name allowlist
  `bootstrap_erased_len_generic_is_safe`, again only honoured under
  `SIMPLE_BOOTSTRAP=1` (`_Items/declaration_lowering.spl`).

Only 71 of 667 closure modules had reached HIR when the lane died, so the two
sibling helpers were the next fatals in line.

The helpers were introduced by `78dbaff5d7c` ("chore: sync and checkpoint
local changes", 2026-08-08) with no stated rationale; `513321c54f5` did not
add them. The same file already calls `.len()` directly on arrays, so the
helper carried no interpreter-cost property to preserve.

## Fix

- HIR: `eprint` moved into `is_interp_builtin_fn` (unconditional).
- MIR: `eprint(x)` lowers via `lower_bootstrap_print_call(args, "rt_eprintln")`,
  exactly as `println` -> `rt_println`.
- Runtime: new `void rt_eprintln(const char*)` in `runtime_native.c`
  (`spl_eprintln`: stderr + newline, matching the seed's `eprint` semantics in
  `interpreter_eval.rs:228`). Additive; no existing signature changed.
  LLVM backend declares `@rt_eprintln(ptr)` next to `@rt_println`.
- Source: the three `<T>` len helpers replaced by `.len()` at all 50 call
  sites (36 + 11 + 3); the now-dead allowlist and its env gate deleted.
- Spec: `test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl`
  (2 of 3 fail pre-fix, 3/3 pass post-fix).
- Guard: `scripts/check/check-no-free-generic-fn-in-bootstrap-closure.shs`
  (`--selftest` 6 fixtures, fail-closed verdict convention, baseline in
  `scripts/check/free_generic_fn_bootstrap_closure_baseline.txt`).

## OPEN: `src/compiler/20.hir/generated/hir_visitor.spl`

23 generated `walk_hir_*<C>(node, ctx: C, f: fn(HirWalkNode, C) -> C) -> C`
walkers are free generic functions, and the module is in the bootstrap
closure via `35.semantics/enum_contract/hir_match_coverage.spl:30`
(`walk_hir_expr`). They are genuinely polymorphic in the accumulator and
cannot be de-generified by hand -- the generator is
`src/app/compiler_schema/visitor_gen.spl`. Options: emit a concrete
accumulator type per consumer, or land #158 Phase B. Until then they are
baselined by the guard above and WILL fatal once HIR lowering reaches that
module on a lane without `SIMPLE_BOOTSTRAP=1` (and with it too, since they
were never on the allowlist). Not reached in the fp9 log (died at module 71).
