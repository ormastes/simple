# Interpreter rejects index assignment into a fixed-size array (`var a: [i64; 64]`)

- Status: OPEN (2026-09-12) — found by the interpreter perf probe hunt; correctness gap, not perf
- Found: 2026-09-12
- Component: seed tree-walk interpreter, index-assignment path (`Value::FixedArray`/sized array vs `Value::Array`)
- Lane: interpreter (`SIMPLE_EXECUTION_MODE=interpreter`); JIT not yet checked

## Reproduction

```simple
fn main():
    var arr: [i64; 64] = [0, 0, 0, ...]   # 64 zeros
    var i = 0
    while i < 100:
        arr[i % 64] = i
        i = i + 1
    print("{arr[1]}")
```

Deployed seed `bin/release/aarch64-unknown-linux-gnu/simple` (2026-09-06 09:59):

```
error: semantic: invalid assignment: cannot index assign value of type array
```

The same loop over a growable `var arr: [i64] = []` filled with 64 pushes
works. The test tree only exercises fixed-size arrays as `val`/read-only, so
nothing pinned the mutable case.

## Fix direction

Extend the index-assignment `store_last` / place-write arm
(`src/compiler_rust/compiler/src/interpreter/place.rs`, `store_last`, the
`Value::Array` case) to the sized-array value kind with the existing bounds
error text; pin with a lang unit spec that writes, reads back, and checks that
size-changing methods are still rejected (`handle_fixed_array_methods`).

## Related

- probe hunt report `probes/hunt/REPORT.md` (2026-09-12 session), shape `fixed_array_ops`
