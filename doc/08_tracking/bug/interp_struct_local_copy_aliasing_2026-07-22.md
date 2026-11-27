# Bug: interpreter struct locals alias instead of copy on assignment

## Resolution 2026-11-25 — does not reproduce on the pinned seed

- **verified fixed (STALE)**: on the pinned Rust seed (`bin/simple.exe`
  v1.0.0-rc.1, Windows), both lanes (`bin/simple.exe run` default and
  `SIMPLE_EXECUTION_MODE=interpreter`):
  - The doc's minimal repro (`var b = a; b.x = 2`) prints `a.x=1 b.x=2` —
    copy semantics hold.
  - The uart16550-shaped variant (struct passed by value into a function,
    `var out = state; out.mcr = value; return out`) prints
    `old mcr=1 new mcr=26 lcr=3 count=7` — the source struct is untouched.
- The in-tree workaround (`uart_latch_msr_delta` capturing pre-mutation scalar
  lines in `src/lib/hardware/soc_rtl/uart16550.spl`) remains harmless and was
  left in place; removing it is optional cleanup, not required for correctness.
- Status: OPEN -> **RESOLVED (does not reproduce)**.

- **ID:** interp_struct_local_copy_aliasing
- **Date:** 2026-07-22
- **Status:** RESOLVED 2026-11-25 (does not reproduce on pinned seed; see top)
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
