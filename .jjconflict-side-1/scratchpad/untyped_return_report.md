# Untyped-return functions on the native --entry path — fix report

Date: 2026-07-13. Worktree: /tmp/wt_untypedret @ 35c4b52ead6, healed with
ed26f0f0159 frontend/MIR files (broken half-finished lexer migration in base,
per coordinator). Patch: `scratchpad/untyped_return.patch`.

## Problem

`fn pick(n: i64): return n * 3` (no declared return type) compiled to invalid
LLVM IR on the native --entry path: the function was emitted as `void` while
the `return` carried a real value → `%t0 = bitcast i64 %l8 to void; ret void
%t0` → llc rejected it with the cryptic, far-from-the-cause "void type only
allowed for function results". The oracle (interpreter) handled it fine.

## Route chosen: (a) inference, with (b) fatal error as the fallback

Both routes implemented; inference is preferred, and every case inference
cannot decide safely falls through to the clear fatal error.

- **(a)** If all `return <value>` sites in an unannotated function agree on
  ONE simple concrete type (i64/i32/u64/u32/f64/f32/bool/text — literal,
  param reference, arithmetic over agreeing operands, comparison/logical
  (bool), unary neg/not, cast), the return type is promoted from the Unit
  default to that type.
- **(b)** Otherwise (disagreeing sites, or any un-inferrable shape — which
  deliberately includes ALL calls, so self-recursion is conservatively
  covered) → fatal HIR error:
  `untyped function returns a value: function 'X' returns a value but
  declares no return type; add '-> T'` — allowlisted in
  `_hir_lowering_error_is_fatal` (driver.spl) so it stops the build.

### Key design point: inference runs in the signature pass, not body lowering

A function's return type is registered on its symbol during the module's
up-front signature-declaration pass (`declare_module_symbols` /
`register_imported_symbol` in module_lowering.spl), which is what CALLERS
consult for `val v = f(...)`. Inferring after `f`'s body is lowered would fix
`f`'s own `ret` but leave every call site void. So the scanner walks the raw
parser AST (`Function.body`) during that pass; `lower_function`
(declaration_lowering.spl) then just reads the decided type back off the
function's own symbol. Verified end-to-end: the first attempt (inference
inside `lower_function` only) built but printed `0` instead of `12` —
exactly the caller-side hole; the signature-pass version prints `12`.

Procedures (no return-with-value anywhere) keep the Unit default unchanged;
unhandled/rare expression shapes are not descended into (conservative:
exactly as broken/working as before). Lambdas are not descended into (their
`return` belongs to the closure). Gated off under SIMPLE_BOOTSTRAP (that
path uses `bootstrap_builtin_return_type` and is owned by the parallel
redeploy lane).

## Files changed (all in owned scope)

- `src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl` —
  `ReturnScan` struct + merge, BinOp classifiers, simple-type-name helpers.
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` —
  `infer_untyped_return_type` + AST scanners (`scan_ast_block/stmt/expr`,
  `infer_simple_type_name_ast`); the two `has_return_type ? lower :
  Unit-default` sites now call the inference instead of hard Unit.
- `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` —
  `lower_function` reads the inferred return type back from the symbol for
  unannotated functions.
- `src/compiler/80.driver/driver.spl` — added
  `"untyped function returns a value:"` prefix to the fatal allowlist.

## Battery (native vs oracle; oracle = `env -u SIMPLE_BOOTSTRAP bin/simple run`)

| # | Case | Oracle | Native (build/run/out) | Verdict |
|---|------|--------|------------------------|---------|
| 1 | untyped fn returning i64, called+printed (ur1) | 12 (`<value:0xc>`) | build 0, run 0, `12` | PASS — was the invalid-IR case; now oracle-equal |
| 2 | untyped procedure (b2_proc) | `hi \nworld` | build 0, run 0, `hi \nworld` | PASS — still Unit, unchanged |
| 3 | typed fn control (ur3) | 12 | build 0, run 0, `12` | PASS — unchanged |
| 4 | untyped fn, return in both if branches (b4_ifboth) | -9 | build 0, `-9` (run rc=1) | PASS — output oracle-equal; rc=1 is PRE-EXISTING: fully-typed control b4_typed gives identical build 0 / `-9` / rc=1 |
| 5 | multi-construct: typed fn + procedure + fixed case (b5_multi) | `start` `17` | build 0, `start`/`17` (run rc=1, same pre-existing shape as #4) | PASS |
| 6 | ambiguous (i64 vs text branches) (b_ambig) | runs (dynamic, prints 5) | build EXIT 1, NO binary, clear fatal: `untyped function returns a value: function 'ambiguous' ... add '-> T'` | PASS — route (b) loud + actionable |
| 7 | self-recursive untyped fn (b_rec) | — | build EXIT 1, NO binary, 1x fatal `untyped function returns a value` message | PASS — route (b): `return count(n-1)` is a Call → un-inferrable → fatal, verified empirically |

Note on #4/#5 rc=1: the process exit code for this program shape is 1 even
with a fully-annotated control (`b4_typed.spl`, zero inference involved), so
it is independent of this change; stdout is oracle-equal in all cases.

## Smoke matrix

`sh scripts/check/native-smoke-matrix.shs` (run on the healed worktree with
the fix applied):

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

All 15 cases: arith_fn_call PASS, if_elif_else PASS, while_sum PASS,
for_in_array PASS, array_index_rw PASS, struct_field PASS, enum_construct
PASS, enum_match PASS, string_concat_len PASS, string_interp PASS,
nested_fn_3deep PASS, closure_lambda PASS, dict_index PASS,
option_nil_check FAIL (the single allowed failure per gate), result_try_op
PASS. Gate (>=14/15, 0 codegen_fallback_hits, only allowed fail =
option_nil_check) MET exactly.

Additional regression checks: trivial `fn main(): print(41)` builds+runs
(rc 0, prints 41); no compiler/stdlib module in the full closure trips the
new fatal error (0 occurrences of the message in passing build logs).

## Not covered / notes

- Battery `.spl` sources preserved in the session scratchpad
  (`ur1/b2_proc/ur3/b4_ifboth/b4_typed/b5_multi/b_ambig/b_rec/triv.spl`).
- Worktree base 35c4b52ead6 was globally broken for native builds (swept
  half-finished lexer migration); healed by checking out 5 frontend/MIR
  files from ed26f0f0159 per coordinator instruction. None of those files
  carried this fix's changes.
- The interpreter/oracle path is untouched (inference only changes what was
  previously a hard `Unit` default on the HIR signature pass, plus the
  fatal-allowlist entry in driver.spl).
