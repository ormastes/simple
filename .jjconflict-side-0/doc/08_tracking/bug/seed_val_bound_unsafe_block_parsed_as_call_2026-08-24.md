# Seed interpreter parses a `val`-bound `unsafe(...)` block as a call to a function named `unsafe` (2026-08-24)

- **Status:** Parser/HIR source fix implemented and focused-tested; seed deploy
  and imported execution remain pending
- **Severity:** HIGH — it made `native-build` fail with a diagnostic that named
  neither the file, the function, nor the construct
- **Area:** seed interpreter / parser (`src/compiler_rust`)
- **Found by:** clearing the `arm_body` arena defect
  (`io_runtime_import_breaks_native_build_len_on_i64_2026-08-24.md`) and hitting
  the next blocker underneath it

## Six-line reproducer

```
extern fn rt_getpid() -> i64

fn main() -> i64:
    val p = unsafe(capabilities: [ffi]):
        rt_getpid()
    print("p_ok={p > 0}")
    return 0
```

```
<seed> run ub.spl
-> error[E1002]: function `unsafe` not found
   = help: check the function name or import the module that defines it
```

The STATEMENT-position form is fine and is what the rest of the tree uses:

```
fn my_pid() -> i64:
    unsafe(capabilities: [ffi]):
        rt_getpid()
```

That builds, links and runs (verified). So the defect is specific to binding an
`unsafe` block-expression to a `val`/`var`: the seed reads
`unsafe(capabilities: [ffi])` as a call expression whose callee is the
identifier `unsafe`, then fails to resolve it.

## Why it was expensive to find

The message is raised by the SEED
(`compiler/src/interpreter_call/mod.rs:787`) while it interprets the
pure-Simple compiler, so it carries no `.spl` location and mentions no
user-visible construct. On the four-line `std.io_runtime` fixture the output was
exactly two lines — `error[E1002]: function 'unsafe' not found` and a generic
help — after 1,780 lines of build progress.

The technique that pinned it in a single run is the same one that pinned the
`arm_body` defect: add `crate::interpreter::debug_call_stack_snapshot()` to the
error site under the existing `SIMPLE_INTERP_OOB_DEBUG` gate, and run with
`SIMPLE_DEBUG_FIELD_ACCESS=1` so the stack is populated. That printed:

```
main -> ... -> lower_to_mir -> lower_module -> lower_function -> ...
     -> lower_expr_impl -> lower_method_call -> mir_log_conv_trace_on
```

naming `mir_log_conv_trace_on` directly.

## The three sites in the tree

A repo-wide scan (`grep -rn "=\s*unsafe(" src/compiler --include='*.spl'`)
finds exactly three:

| site | status |
|---|---|
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:46` (`mir_dict_elem_trace_on`) | FIXED — moved to a helper |
| `50.mir/_MirLoweringExpr/method_calls_literals.spl:56` (`mir_log_conv_trace_on`) | FIXED — same helper |
| `20.hir/hir_lowering/_Expressions/expression_support.spl:492` (`composite_metadata_missing`) | LEFT ALONE |

The two fixed sites are level-gated trace gates reached from `lower_method_call`,
so **any** program whose lowering touched a method call hit them. They now read
the environment through one statement-position helper:

```
fn _mir_trace_env_raw(key: text) -> text:
    unsafe(capabilities: [ffi]):
        rt_env_get(key) ?? ""
```

The `?? ""` is load-bearing: without it the helper fails with
`nil is forbidden by the non-optional return contract of '_mir_trace_env_raw'`,
because `rt_env_get` is declared `-> text` but the runtime hands back nil for an
unset variable. The original inline form did not surface that because the value
was never returned across a function boundary.

The third site is deliberately NOT converted. Its block body closes over `self`
(`rt_dict_contains(self.struct_field_access_by_name, composite_name)`) and the
field's type is an alias (`HirFieldAccessByName`) that the extern takes as
`i64`, so extracting a helper means asserting a parameter type that the current
code only gets away with through erasure. It was not reached by any build in
this lane, so converting it would be an unverified change to a hot HIR path.

## NOT verified

- The seed-side parser defect itself is not fixed. Only the two call sites are
  worked around.
- Whether the same mis-parse affects `unsafe` blocks bound in other expression
  positions (an argument, a field initializer, a match scrutinee) was not tested.

## 2026-08-24 (later) — the third site WAS reached, and is now fixed too

The judgement above ("not reached by any build in this lane, so converting it
would be an unverified change") was correct at the time and wrong an hour later.
`native-build src/app/mcp/main.spl` reaches it: with the two MIR gates fixed the
MCP build got past parse for all 61 modules and then died at HIR 8/61 with the
same `function 'unsafe' not found`. The interpreted call stack under
`SIMPLE_INTERP_OOB_DEBUG=1 SIMPLE_DEBUG_FIELD_ACCESS=1` named it directly:

```
... -> lower_and_check_impl -> lower_parser_module_unstub -> lower_module
    -> lower_function -> lower_hir_block -> lower_hir_stmt_multi
    -> lower_hir_stmt -> lower_hir_expr -> lower_hir_expr -> field_access_for_expr
```

The type problem that made it look risky is avoided by making the helper a
METHOD on `impl HirLowering` rather than a free function: `self` stays in scope,
so `self.struct_field_access_by_name` is passed to `rt_dict_contains` exactly as
before and its aliased type (`HirFieldAccessByName`) never has to be spelled as
a parameter. The body is byte-identical to the old block body; only its position
changed.

Measured effect: the MCP build advances from **HIR 8/61** to **MIR 61/61** —
every one of the 61 modules now parses, lowers to HIR, and lowers to MIR. It
then stops on a FOURTH, unrelated defect: MIR lowering has no assignment-target
support for a tuple, so `(cwd, _rc) = shell_cmd("pwd")`
(`src/app/mcp/main_lazy_protocol.spl:63`) fails with
`unsupported MIR assignment target: HirExprKind::TupleLit(...)`
(`50.mir/mir_lowering_stmts.spl:1740`). That is recorded separately.

All three `= unsafe(` sites in `src/compiler/**` are now converted; a re-scan
returns none.

## 2026-08-24 direct parser fix

The seed parser now recognizes colon-terminated lexical unsafe blocks from
primary-expression position. It shares one block parser with statement
position and retains ordinary `unsafe(...)` calls when no colon follows the
matching parenthesis. The focused parser test exercises both forms, and the
focused compiler test proves the value-bound HIR remains an unsafe boundary
with the block tail's `i64` type.

The fix is compile-time only and linear in the short capability header. It
does not add a helper call or any target-runtime allocation, copy, closure, or
dispatch. The earlier pure-Simple helper workarounds are not evidence that the
rebuilt seed is admitted; deployment and imported-module execution remain
pending.
