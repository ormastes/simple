# Redeploy Kit 01 — `print(array)` value-based display

## Defect
`print([1, 2, 3])` on the deployed binary emits an ASLR-nondeterministic heap
address tag `<array@0x...>` instead of the element values. This is a
determinism / tool-qualification defect (a certified tool must produce
reproducible output).

Repro (frozen binary):
```
$ simple run - <<'EOF'
fn main(): print([1,2,3])
EOF
<array@0x2e3e605e0c0>   # address changes every run (ASLR)
```

## Root cause
The `run`/JIT execution path uses the native runtime's value formatter, not the
tree-walking core interpreter (`src/compiler/10.frontend/.../value.spl::val_to_text`,
which already renders `[1, 2, 3]`). The native formatter is
`src/compiler_rust/runtime/src/value/sffi/io_print.rs`. Its
`heap_value_to_display_string` had:

```rust
HeapObjectType::Array => format!("<array@{ptr:p}>"),
```

i.e. it printed the heap POINTER for every array, never the contents.

## Fix (implemented)
`src/compiler_rust/runtime/src/value/sffi/io_print.rs`:
- Threaded a `depth` parameter through `value_to_display_string` /
  `heap_value_to_display_string` (public signature unchanged — a 0-depth
  wrapper preserves all call sites).
- Added `array_value_to_display_string(v, depth)` that reads the array with the
  packing-aware `rt_array_len` / `rt_array_get` accessors and renders
  `[e0, e1, ...]`, recursing per element.
- Bounded recursion with `MAX_DISPLAY_DEPTH = 32` (renders `[...]` beyond that)
  to guard against self-referential/cyclic arrays.

Only the `Array` arm changed; `Dict`/`Tuple`/`Object`/`Closure`/`Enum` keep the
address tag (out of scope, separate items).

## Test plan
- Rust unit tests (added, same file, run now): value-based `[1, 2, 3]`, empty
  `[]`, nested `[[1, 2], 3]`, and a "never contains `array@`" assertion.
- Expected-behavior spec: `test/cert/redeploy_pending/print_array_value_based.spl`
  (fails on frozen binary → lives in the non-run redeploy_pending dir).

## Verify-now vs redeploy-pending
- VERIFIED NOW: `cargo test -p simple-runtime --lib io_print` — 30 pass,
  including the 4 new array-display tests. The display logic is correct in
  isolation.
- REDEPLOY-PENDING: end-to-end `simple run print_array_value_based.spl` still
  prints `<array@0x...>` until the runtime is rebuilt and the binary redeployed.
