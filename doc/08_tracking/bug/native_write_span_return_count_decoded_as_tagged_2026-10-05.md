# Native lane: `write_span` return count is decoded as a tagged value (count / 8) (2026-10-05)

**Status:** FIXED on branch `work/write-span-raw-count`. Present on `origin/main` from at least `4b618f09c7a` until that branch.

## Reproduction

`test/fixtures/compiler/write_span_native_inrange_probe.spl` contains
`val moved = fb.write_span(fb, 0, w * 10, w * 50)` with `w = 320`, so the call
writes 16,000 elements.

| lane | printed `moved` | framebuffer checksum |
|---|---|---|
| interpreter | 16000 | 902858392 |
| JIT (`simple run`) | 16000 | 902858392 |
| `SIMPLE_NATIVE_BUILD_RUST=1 native-build` (C runtime from `src/runtime`) | **2000** | 902858392 |

The array contents were correct in every lane; only the returned count was
wrong (16000 / 8 = 2000; 320 / 8 = 40 in the per-row loop).

## Root cause

The three components disagreed on the return contract of `rt_array_write_span`:

| component | contract |
|---|---|
| C twin (`runtime_native.c`) | raw `int64_t` count |
| pure-Simple MIR lowering (`lower_unresolved_array_write_span`) | `-> i64`, raw |
| seed `RuntimeFuncSpec` | `&[I64]`, raw |
| seed Rust runtime | **tagged** `RuntimeValue::from_int(count)` |
| seed codegen (Cranelift builtin dispatch, `calls.rs` runtime-call path, LLVM method table) | consumes the result as a **tagged** value (`write_span` is typed `Any`) |

The seed codegen and the seed runtime matched each other, so the JIT was
right. A seed-compiled native binary links the C twin instead, which returns
the raw count. The tag decode then shifted it right by 3.

Typing `write_span` as `i64` in the seed HIR does not fix it on its own. That
change routes the call through `MethodCallStatic`, whose vtable fallback
references `rt_method_not_found`, a symbol the C runtime did not define.

## Fix

1. The seed Rust runtime returns a **raw** `i64` count, so every runtime and
   lowering now uses one contract.
2. The seed codegen tags the raw count where it consumes the result as a
   tagged value: `(v << 3) | INT(0)`, exactly `rt_value_int(v)`. This applies
   to Cranelift builtin dispatch, the Cranelift `calls.rs` runtime-call path,
   and the LLVM method table.
3. The C runtime gains `rt_method_not_found`, the twin of the seed
   runtime's. It prints the same diagnostic and exits 70. Without it, current
   main cannot link any seed-native binary that makes a typed array method
   call, so the native lane could not run this probe at all.

## Evidence

- `test/fixtures/compiler/write_span_count_lane_probe.spl` prints
  `a=8 b=5 c=0 d0=2 d4=6 d9=0` in the interpreter, the JIT and the native lane.
  Before the fix the JIT printed `a=1` with only the runtime change, and the
  native lane did not link.
- `write_span_native_inrange_probe.spl` gives `moved=16000 … sum=902858392` in
  all three lanes. It asserts the per-row count again.
- `write_span_lane_parity_probe.spl`: the out-of-range error is identical in
  all three lanes (rc 1).
