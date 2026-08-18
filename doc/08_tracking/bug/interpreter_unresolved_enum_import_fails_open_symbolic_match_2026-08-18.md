# Interpreter: unresolved enum import fails open — variant access and match work symbolically

Status: OPEN (advisory; found while sabotage-testing check-bootstrap-preflight.shs)
Date: 2026-08-18
Area: seed interpreter, import/type resolution

## Symptom (measured, not inferred)

A program importing a NONEXISTENT name from a real stdlib module runs to
completion with exit 0 and semantically "correct" output:

```
use std.binary_io.{ByteOrderX}          # ByteOrderX does not exist anywhere
fn order_name(o: ByteOrderX) -> text:
    match o:
        case ByteOrderX.LittleEndian: "little"
        case ByteOrderX.BigEndian: "big"
fn main():
    print(order_name(ByteOrderX.LittleEndian) + "," + order_name(ByteOrderX.BigEndian))
```

Under the current seed (`bin/simple run`, rebuilt 2026-08-18 06:12) this prints
`little,big` and exits 0. The import failure is only a WARN:
`[WARN] Failed to load imported types from ["std", "binary_io"]: ...`.
`ByteOrderX.LittleEndian` evaluates to a name-symbolic value that its own
`case` pattern then matches — even discriminating variants correctly — so an
entirely unresolved enum behaves like a real one.

## Why it matters

- Any T0 probe of the form "does this import/type resolve?" is VACUOUS under
  the interpreter: it passes when the import is broken. The preflight probe in
  `scripts/check/check-bootstrap-preflight.shs` was strengthened (two-variant
  discrimination) and its mutation proof had to sabotage the mapping, not the
  type name, because a wrong type name cannot make the run fail.
- Same fail-open family as `mir_unresolved_method_const0_fails_open_2026-07-28.md`
  and `case_bare_ident_is_irrefutable_binding_2026-08-01.md`, but this is
  interpreter-side import/type resolution, not MIR lowering.

## Expected

An unresolved imported type used as a value/pattern should be a hard error (or
at minimum make `run` exit nonzero), not a WARN followed by symbolic execution.
