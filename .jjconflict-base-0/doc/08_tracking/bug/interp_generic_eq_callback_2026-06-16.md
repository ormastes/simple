# Bug: generic `!=` / 2-arg `==` on `[T]` elements mis-evaluates in interpreter

**Found:** 2026-06-16 · **Severity:** P2 (correctness) · **Area:** interpreter / generics
**Status:** source fixed; focused seed-interpreter execution pending

## Summary
Inside a generic function `fn f<T>(data: [T], ...)`, comparing two array elements of the
generic type with `!=` (or `==`) evaluates incorrectly through the resolved-module path:
`data[i] != data[i - 1]` does not reflect actual inequality, so consumers like a
`unique`/dedup loop collapse or mis-keep elements. A two-argument callback
`eq: fn(T, T) -> bool` whose body is a compound boolean (`a == b`, or `if a<b: return false
…`) shows the same wrong result. A single-relational `less: fn(T, T) -> bool` body (`a < b`)
evaluates CORRECTLY — `compute_min_element`, `compute_lower_bound`, and
`compute_binary_search` all pass using exactly that form.

## Repro (minimal)
```simple
fn dedup<T>(data: [T]) -> [T]:
    var out: [T] = []
    if data.len() == 0:
        return out
    out.push(data[0])
    var i = 1
    while i < data.len():
        if data[i] != data[i - 1]:   # <-- mis-evaluates for generic T
            out.push(data[i])
        i = i + 1
    return out
# dedup([1,1,2,3,3,3,1]) should be [1,2,3,1]; observed length collapses.
```

## Discriminator
- `less(a, b)` with body `a < b` (single relational) → correct.
- `a != b` / `a == b` / compound-bool callback body on generic T → wrong.
So the fault is in generic `==`/`!=` (and compound boolean) dispatch on `[T]` element
values, not in callback invocation per se.

## Workaround (in use)
Derive equality from a `less` comparator entirely in the caller body:
`same = (not less(a, b)) and (not less(b, a))`. Applied in
`src/lib/nogc_async_mut/compute/compute_algo_ext.spl` (`compute_unique` takes
`less: fn(T,T)->bool`, not `eq`). The compound `and` lives in normal function-body code
(which is fine); only the generic `==`/`!=` element op is avoided.

## Fix direction
Investigate generic operator lowering for `==`/`!=` on type parameters in the interpreter
(likely a missing/incorrect monomorphized equality dispatch). Related memory:
`feedback_array_get_index_ge1_corruption`, `unit`/`val` identifier traps.

## Discovered by
The std.compute parity build (feature `gpu_containers_unified`) while implementing
`compute_unique`. Co-goal: "find + fix bugs while building the compute stdlib."

## Resolution status (2026-07-15)

Current seed-interpreter array indexing preserves the element `Value`, generic
function calls bind those values directly, and shared equality handles integer
elements without a monomorphized callback path. Multi-field pattern binding also
uses the current tuple-payload field order. No production equality patch is
therefore justified without a fresh failing execution. A focused driver
regression runs the original generic `dedup<T>` form and encodes the complete
`[1, 2, 3, 1]` result as `41231`; execution remains pending a runnable Rust
test artifact.
