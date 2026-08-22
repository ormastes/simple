# stage1 HIR fatals on lexer.spl: `unresolved name: eprint` and a `<T>` array-len helper

**Status:** FIXED (eprint, three `<T>` len helpers); walkers follow-up FIXED 2026-08-22 via #158 Phase B (see bottom); NEW open sibling: fn-typed parameter call links as undefined symbol
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

## FIXED 2026-08-22: walkers go through #158 Phase B (option A, monomorphization)

Option A was chosen because `40.mono` already had the machinery: since
2026-08-21 `monomorphize_integration.spl` specializes free generic fns per
call-site type args, mangles, repoints the call and prunes the template
(pinned by `hir_monomorphization_rewrite_spec.spl`). It was reachable by
nothing, for three reasons, all fixed here:

1. **The Phase A gate fired in HIR lowering, before mono ran.**
   `_Items/declaration_lowering.spl` no longer errors on a generic fn; it
   lowers it with `is_generic_template: true`. Any call site the pass cannot
   rewrite is still fatal (driver `E-MONO-033`), so an unmonomorphized
   generic never reaches MIR.
2. **`SIMPLE_BOOTSTRAP=1` skipped the pass** (`driver_hir_pipeline_passes.spl`).
   Every stage lane exports that var. Only the explicit
   `SIMPLE_BOOTSTRAP_SKIP_MONO=1` escape remains; the driver now prints a
   `[mono] generic_fns=.. call_sites=.. specializations=.. unresolved=..`
   receipt so a stage log proves the pass ran.
3. **The pass only worked inside one module.** Its `sym_names`/`fn_returns`
   maps were keyed by a global `i64` SymbolId although ids are per module
   (module B's symbol 5 resolved to module A's generic at id 5); a
   cross-module callee arrives as `NamedVar("lib.fn")` (qualified display
   name) which never matched the bare template name; the repointed callee
   was `Var(fresh id)`, which MIR's `lower_call` resolves through the
   CALLER's symbol table where a mono symbol does not exist; a bare
   function-reference argument (`walk(e, acc, collect)`) and a constructor
   call `MatchSiteScan(...)` (HIR: `Call(NamedVar("MatchSiteScan"))`) had no
   local type, so `C` was uninferable; and `Named` types were mangled by
   module-local symbol id. Now: maps keyed `"<module>#<id>"`, qualified
   callee resolved by last segment when the qualifier agrees with the
   template's module, callee repointed as `NamedVar(sym, "<qual>.<mangled>")`,
   function references type as `fn(params) -> ret`, non-generic
   constructors type as their `Named`, and `Named` mangles by declared name.

Evidence: 2-module fixture (`pick_second<C>` at i64 and a struct, plus a
nested generic call `same<C>` -> `pick_second`) through the in-process
pure-Simple driver (`bin/simple run src/app/cli/bootstrap_main.spl
native-build main.spl`): `[mono] generic_fns=2 call_sites=4
specializations=3 unresolved=0`, binary printed `35 103 7`, rc=0. Pre-fix:
HIR fatal. Spec `test/01_unit/compiler/mono/free_generic_fn_two_module_native_spec.spl`
0/3 pre-fix, 3/3 post-fix. Non-generic modules are untouched: the pass
returns its input when it finds no template (`process_modules` early return).
Guard `check-no-free-generic-fn-in-bootstrap-closure.shs` keeps the 23 walkers
baselined as an INVENTORY (header rewritten): they still exist as free
generic fns; they are now monomorphized rather than refused.

Gated probe: `SIMPLE_MONO_DIAG=1` traces every function/stmt/expr the pass
visits and every argument it could not type.

## OPEN sibling (found 2026-08-22, not caused by mono): calling a fn-typed parameter

On the same in-process native path, a NON-generic
`fn apply(x: i64, f: fn(i64) -> i64) -> i64: f(x)` links with
`ld.lld: error: undefined symbol: f` -- MIR's `lower_call` treats the
parameter as a direct callee by name (`local_map` does not demote it).
Reproduces single-file, with and without `SIMPLE_BOOTSTRAP=1`. The
walkers call `f(node, acc)`, so after monomorphization the stage lane will
hit THIS at link time for `hir_visitor.spl`. Separate defect, separate fix.
