# Sorting a tagged array that holds wide (heap-boxed) i64 leaves it unsorted

- Date: 2026-10-20
- Status: open (pre-existing; found while fixing jit_array_store_wide_i64_leak_2026-10-20)
- Binary: Rust seed JIT, base dacf1e81637

Reproducer (JIT; the interpreter is correct):

```
fn main():
    var s: [i64] = [0; 3]
    s[0] = 8070450532247928832
    s[1] = 0 - 8070450532247928832
    s[2] = 5
    s.sort()
    print "{s[0]} {s[1]} {s[2]}"   # prints the original order
main()
```

Cause: `rt_array_sort` -> `primitive_sort::sort_runtime_values` / the array_sort
provider compare tagged words and ignore `HeapInt` boxes (values outside the
61-bit inline range). Arrays packed by the `[i64]` word lane sort correctly
(signed raw words); an array that cannot pack (non-integer slot, threads already
started, or unpacked once) still hits this. Fix: decode `as_heap_i64` in the
comparator. Probe: removed with the #3989 revert (use the inline reproducer above).

Note (2026-10-20): restored by the #3989 revert. The paragraph above that says packed arrays sort correctly describes the reverted word lane; the bug itself is independent of it.
