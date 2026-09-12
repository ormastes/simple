# Bug: interpreter struct locals alias instead of copy on assignment

- **ID:** interp_struct_local_copy_aliasing
- **Date:** 2026-07-22
- **Status:** CLOSED (2026-09-12) — not reproducible; see "Re-check 2026-09-12"
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

## Re-check 2026-09-12

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1`.

Repro exactly as the sketch above, inside a function body:

```simple
struct S:
    x: i64

fn probe() -> str:
    var a = S { x: 1 }
    var b = a
    b.x = 2
    return "a.x=" + str(a.x) + " b.x=" + str(b.x)

print probe()
```

```
$ bin/simple run probe.spl                                 -> a.x=1 b.x=2
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl -> a.x=1 b.x=2
```

Both engines copy. **Not reproducible** — status CLOSED.

Regression guard landed: `test/01_unit/bugs/interp_struct_local_copy_aliasing_spec.spl`
(4 examples, including the `uart16550.spl` before/after shape).

```
SPEC FILE VERDICT: test/01_unit/bugs/interp_struct_local_copy_aliasing_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0
```

Non-vacuity proof (spec discriminates): flipping the two source-struct
assertions to the documented buggy value (`a.x == 2`, i.e. aliasing) turns the
same file RED —
`outcome=ERROR declared>=4 executed=4 passed=2 failed=2 skipped=0 dropped=0`.

### Adjacent live defect found during this re-check (NOT this bug)

The copy is correct **inside a function**. At **module/top-level scope** a
field assignment to a module-level `var` is silently dropped on both engines —
see `doc/08_tracking/bug/top_level_field_and_index_assign_dropped_without_loop_2026-09-12.md`.
