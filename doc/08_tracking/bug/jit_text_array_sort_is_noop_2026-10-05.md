# JIT `[text].sorted()` / `.sort()` returned the input order unchanged

- Status: FIXED (Rust and C runtime lanes), 2026-10-05
- Found while root-causing why the light test daemon lane never routes; see
  `macos_test_runner_startup_ps_spawn_and_dead_daemon_2026-10-04.md`

## Symptom

```simple
val s = ["pear", "apple", "zeta", "mango"].sorted()
# interpreter: apple,mango,pear,zeta
# seed JIT:    pear,apple,zeta,mango   <- unchanged
```

## Root cause

`rt_array_sorted` and `rt_array_sort` sort through `rt_sorted_value_cmp`:
- Rust lane: `src/compiler_rust/runtime/src/value/collections.rs`
- C lane: `src/runtime/runtime_native.c`

That comparator ordered unsigned boxes, ints and floats, and compared every
other pair as `Equal`, which includes text vs text. A stable sort of
all-Equal elements keeps the input order.

In the C lane, `rt_array_sort` already went through `rt_sort_cmp`, which does
order text, so only the C `rt_array_sorted` was affected there. The interpreter
compares text with `a.cmp(b)`, i.e. byte order.

## Impact found

The test daemon's environment identity digest sorts its `name=value` rows.
- The test client is JIT-compiled, so it hashed the rows unsorted.
- The daemon runs interpreted, so it hashed them sorted.

The digests therefore never matched, and every request was sent down the
direct lane with the message "environment-identity: caller environment
differs". This does not depend on the host OS.

## Fix

Both lanes now compare text vs text byte-lexicographically: the shorter prefix
comes first, and the result is identical to Rust `String` ordering. Every other
pair keeps its old ordering.

## Specs

| spec | covers |
|---|---|
| `collection_tests::test_array_sorted_orders_text_like_the_interpreter` | exact repro |
| `collection_tests::test_array_sort_and_sort_desc_order_text_bytewise` | generalization: in-place `sort`, `sort_desc`, prefixes, case, UTF-8, empty string |
