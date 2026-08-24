# Seed interpreter parses a `val`-bound `unsafe(...)` block as a call to a function named `unsafe` (2026-08-24)

- **Status:** OPEN in the seed; the three affected compiler call sites are being
  worked around in pure Simple (2 fixed, 1 left alone — see below)
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
