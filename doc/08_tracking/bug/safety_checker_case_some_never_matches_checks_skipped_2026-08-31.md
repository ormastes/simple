# Safety checker's `case Some` arms never match — E1047 and transfer checks are silently skipped

- **Filed:** 2026-08-31
- **Status:** OPEN — diagnosed, deliberately NOT fixed here (see "Why not fixed in this lane")
- **Severity:** correctness. Diagnostics that are supposed to fire never fire.
- **Component:** `src/compiler/35.semantics/safety_checker.spl`, `safety_checker_expr.spl`, `safety_checker_transfer.spl`

## The defect

Three lookup helpers are declared as returning a plain nullable and return a
**bare** value, never a `Some(...)` box:

```
safety_checker.spl:166           fn safety_lookup_param(...) -> SafetyParamTrack?
safety_checker.spl:275           fn safety_lookup_iter(...)  -> SafetyIterTrack?
safety_checker_transfer.spl:137  fn safety_transfer_lookup(...) -> SafetyTransferBinding?
```

Each has the same body shape:

```
for pt in self.context.params:
    if pt.symbol_id == symbol_id:
        return pt          # <-- BARE. not Some(pt)
nil
```

Every caller reads them with `case Some(...)`. An Option arm cannot match a bare
struct value, so **the `Some` arm is never taken and the `nil` arm always is**.
The check bodies inside those arms have never executed.

## What is actually not happening

At `safety_checker.spl:211` and `:223`, the unreachable body is:

```
val msg = "E1047: parameter '{name}' is mutated but not declared mut"
self.context.errors = self.context.errors.push(SafetyError.Other(msg, target.span))
```

So **E1047 is never emitted**. A parameter mutated without `mut` is accepted
silently. The same applies to the iterator-track checks (`:290`, `:300`, `:336`)
and the transfer-binding check (`safety_checker_transfer.spl:168`), plus the
SFFI method-resolution reads at `safety_checker_expr.spl:145,162`.

This is worth separating from the rest of the `case Some` population: most of
those sites corrupt a value or fall back to a default. These **disable a
diagnostic**, and a disabled diagnostic looks exactly like a clean codebase.

## Cause

Instance of the class recorded in
`case_some_on_mixed_population_nullable_slot_2026-08-31.md`: a slot or return
declared `T?` (a plain nullable) but read as though it were an `Option<T>` box.
Repo rule, already stated in-tree: **"a nullable is not an Option box"**
(`statements.spl:409/580`, `module_declarations_bootstrap.spl:435`, bug doc
2026-07-23).

Found by a classified sweep of `case Some(` across `src/compiler`: 467 real
sites, **218** on slots declared as plain nullables (111 of them binding
aggregates), spread over 80.driver 46, 70.backend 40, 50.mir 36, 35.semantics 34.

## Fix

Convert the readers to `.?` + `.unwrap()`, or to `if val`. No change to the
helpers is needed — they already match their declared type; it is the readers
that are wrong.

## Why not fixed in this lane

Fixing this **turns on error paths that have never run**. E1047 firing for the
first time across a 100k-file tree may well reject code that currently compiles,
including the compiler's own sources, which would break the bootstrap this branch
exists to repair. That is a legitimate change to make and probably an overdue
one, but it needs its own lane, its own full build, and its own count of what it
newly rejects — not a drive-by inside a macOS bootstrap fix.

Recorded now, with the exact sites, so the work is not lost.

## Sites

```
safety_checker.spl:211, 223, 248        safety_lookup_param
safety_checker.spl:290, 300, 336        safety_lookup_iter
safety_checker_expr.spl:145, 162        sffi_method_resolution_symbol
safety_checker_transfer.spl:168         safety_transfer_lookup
```
