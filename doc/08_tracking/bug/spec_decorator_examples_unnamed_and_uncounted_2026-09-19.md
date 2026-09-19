# Decorator-invoked examples are reported "unnamed", and the VERDICT's skipped= stays 0 (2026-09-19)

**Status:** open. **Found by:** lane C2 while making a host-dependent spec skip
by named reason instead of passing vacuously.

## Observed

`skip_if(cond, reason)` from `std.spec.decorators` is the repo's mechanism for
a scenario that must not run on this host. Used as

```
val needs_x64 = skip_if(fn(): skip_reason() != "", "x86_64 run environment missing: ...")
needs_x64("links a dynamic ET_EXEC ...", fn(): ...)
```

it behaves correctly on the SKIP side: the line reads
`it <name> ... skipped (<reason>)`, the example does not run, and the verdict's
`executed=` drops accordingly (measured: `executed=1` instead of `7`). Two
things are still wrong.

1. **On the RUN side the example loses its name.** The transcript reads
   `✓ unnamed` for every decorator-invoked example, while a literal
   `it "name":` prints its name. `it` is a lowered BDD form
   (`stmt_lowering.rs`, `rt_bdd_it_start_rv`) whose name argument is taken from
   the call site; reached through a decorator it falls back to the literal
   string `"unnamed"`. The recorded evidence therefore cannot say WHICH
   scenario passed. Worked around in lane C2 by printing
   `scenario: <name>` as the first line of each body — a workaround, not a fix.
2. **`SPEC FILE VERDICT ... skipped=0`** even when six examples were skipped
   and the runner's own summary line says `6 skipped`. The verdict's `skipped=`
   field is what `test_db.sdn` records, so a skipped run looks like a run with
   no skips.

## Why it matters

The whole point of the skip is that a proof which did not run must not be
recorded as a proof that did. Point 2 puts that back: a reader of `test_db`
sees `skipped=0` and no indication that the host requirement was unmet.

## Reproduce

```
bin/simple test --no-session-daemon test/01_unit/compiler/backend/linker/elf_x64_dynamic_exec_spec.spl
SIMPLE_X64_SYSROOT=/nonexistent bin/simple test --no-session-daemon \
  test/01_unit/compiler/backend/linker/elf_x64_dynamic_exec_spec.spl
```

A local probe also showed that a plain helper (`fn scenario(name, body): it(name, body)`)
called as `scenario("x", fn(): ...)` inside a `describe` does not parse
(`expected Colon, found LParen`), so the decorator value is the only form
available — the name loss cannot be side-stepped in the spec.

## Fix direction

Give `rt_bdd_it_start_rv` the runtime name value when the call is not a
literal BDD form, and count decorator skips into the verdict's `skipped=`
field (`test_executor_parsing.spl` already parses `N skipped`; the VERDICT
line is produced elsewhere and does not use it).
