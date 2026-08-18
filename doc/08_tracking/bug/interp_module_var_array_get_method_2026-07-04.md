# Interpreter/compiler: .get(i) on module-level array vars fails with "unknown extern function: rt_args_count"

**Date:** 2026-07-04
**Severity:** medium (silent-ish — semantic error at eval time, misleading message)
**Status:** RESOLVED (2026-08-09, not reproducible — see Re-verification below)

## Symptom

`.get(i)` method calls on MODULE-LEVEL array `var`s fail at evaluation:

```
semantic: unknown extern function: rt_args_count
```

while `.get(i)` on LOCAL arrays works pervasively (e.g. `tokens.get(pos)`
throughout formula.spl).

## Repro context

Found implementing LET's binding stack: module-level
`var _let_names: [text]` / `_let_values: [text]` in
src/app/office/sheets/formula.spl; `_let_names.get(i)` triggered the error.
Isolated via a bisection ladder (stub return → hardcoded index → real call)
to pin the exact broken call form.

## Workaround (in use)

Bracket indexing on module-level arrays: `_let_names[i]` — matches the
established `_di_names[idx]` precedent in di_runtime.spl.

## Next step

The method-dispatch path for module-level var receivers appears to resolve
builtin array methods differently from locals (falls through to an extern
lookup). Likely near the interpreter's method-call resolution for global/
module bindings. Cross-ref the module-var findings ledger:
[[interp_cross_module_struct_field_collision_2026-07-04]] (different bug,
same "module-scope resolution differs from local" family).

## Re-verification 2026-08-09 — NOT REPRODUCIBLE, marking RESOLVED

Reproduced the exact repro shape (module-level `var _names: [text]`, `.get(i)`
called from a function) on the currently deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed-warning banner
confirmed) under both default `bin/simple run` and
`SIMPLE_EXECUTION_MODE=interpret`: `.get(0)/.get(1)/.get(2)` all resolve and
return the correct elements, with no `unknown extern function: rt_args_count`
error. No source change was needed. Regression gate landed:
`test/01_unit/language/module_var_array_get_method_spec.spl` (`3 examples, 0
failures`).

**Status: RESOLVED** (verified fixed upstream, no code change required).

## Execution-based settlement 2026-08-17 — CONFIRMED RESOLVED (both engines GREEN)

The 2026-08-09 stamp above was run-based but recorded no commands or output,
and the named failing symbol (`rt_args_count`) is absent from current source,
so the row could be neither confirmed nor refuted by source inspection. It has
now been settled by execution.

**Binary identity (recorded before AND after the runs — identical, so no run
spans a redeploy):**

```
readlink -f bin/simple
  /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
stat -c '%s %y' "$(readlink -f bin/simple)"
  59621024 2026-08-17 20:28:24.151268554 +0000
```

Still the Rust seed (prints the bootstrap-seed warning banner).

**Minimal repro** (module-level array `var`s, `.get(i)` with both a constant
and a function-parameter index, called from module scope AND from inside a
function — plus the bracket-index workaround for contrast):

```simple
var _let_names: [text] = ["a", "b", "c"]
var _let_values: [text] = ["1", "2", "3"]

fn lookup(i: i32) -> text:
    return _let_names.get(i)

fn main():
    print(_let_names.get(0))
    print(_let_names.get(2))
    print(lookup(1))
    print(_let_values.get(1))
    print(_let_names[1])
```

**Commands and output** (expected: `a c b 2 b`):

```
$ bin/simple run modvar_get.spl                                # JIT
a
c
b
2
b

$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run modvar_get.spl
a
c
b
2
b

$ SIMPLE_EXECUTION_MODE=interpret bin/simple run modvar_get.spl
a
c
b
2
b
```

All three engines produce the correct elements. No `unknown extern function:
rt_args_count`, no error of any kind. Notably there is **no** interpreter-only
divergence here — unlike the class-carrier family
([[interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17]],
where the interpreter is RED and JIT/native GREEN because `Value::ClassInstance`
has zero producers and `class` falls back to the copy-on-write STRUCT carrier).
This row is a **different shape**: it is method *dispatch/resolution* on a
module-scope receiver returning a `text` element, not a value-carrier identity
problem, and it is uniform across engines. No cross-reference defect applies.

**Classification: ALREADY FIXED.** The RESOLVED status above stands, now backed
by reproducible per-engine evidence rather than an unrecorded claim.
