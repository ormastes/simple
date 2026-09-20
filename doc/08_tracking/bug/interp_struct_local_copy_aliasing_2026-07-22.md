# Bug: interpreter struct locals alias instead of copy on assignment

- **ID:** interp_struct_local_copy_aliasing
- **Date:** 2026-07-22
- **Status:** OPEN
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
