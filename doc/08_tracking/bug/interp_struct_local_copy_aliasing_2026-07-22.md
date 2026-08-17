# Bug: interpreter struct locals alias instead of copy on assignment

- **ID:** interp_struct_local_copy_aliasing
- **Date:** 2026-07-22
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** high (silent state corruption)
- **Component:** seed interpreter (value semantics for struct assignment)

## Symptom
In `src/lib/hardware/soc_rtl/uart16550.spl` (`uart_mmio_write`), the pattern:

```simple
var out = state      # struct local, expected value copy
out.mcr = v          # mutates BOTH out and state
```

mutated the source struct as well: comparing `state.mcr` (expected old value)
against `out.mcr` (new value) observed `old_mcr == new_mcr`. Struct locals
alias the source instead of copying under the seed interpreter (`bin/simple run`).

## Impact
Any before/after-state pattern (`val old = s; mutate(s); compare(old, s)`) is
silently corrupted. This contradicts the documented value-type semantics
(arrays/structs passed by copy) and produces wrong results with no diagnostic.

## Workaround (in tree)
Capture derived scalar values BEFORE mutation instead of holding the old
struct: `uart16550.spl` passes the pre-mutation line bits as a `u32`
(`uart_latch_msr_delta(new_state, old_lines)`), never the old struct.

## Repro sketch
```simple
struct S { x: i64 }
fn main():
    var a = S { x: 1 }
    var b = a
    b.x = 2
    print(a.x)   # expected 1; interpreter prints 2
```
Run with the seed interpreter path (`bin/simple run`).

## Fix direction
Struct assignment into a `var` local must deep-copy (as array assignment
does); audit the interpreter's value-clone path for struct rvalues.

## Re-verification 2026-08-17 — DOES NOT REPRODUCE

The doc's verbatim reproducer (`struct S`, `var b = a; b.x = 2; print(a.x)`)
prints `1` — the correct value-semantics answer — on the deployed seed in BOTH
`SIMPLE_EXECUTION_MODE=interpreter` and the default JIT lane. This doc records
the interpreter printing `2`; that no longer happens.

Note this defect is the exact MIRROR of
`interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md`
(which complains that a class field does not alias ENOUGH). Both now behave
correctly, which is consistent with the two having been opposite faces of the
same copy-on-write write-back gate rather than two independent defects.

Not proven: the `src/lib/hardware/soc_rtl/uart16550.spl` observation site
(`uart_mmio_write`) was not re-exercised — only the reduced reproducer.
