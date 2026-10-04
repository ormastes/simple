# JIT: a condition on an `ANY` value tested the tagged word, so `false`/`nil` were truthy

**Date:** 2026-10-05
**Status:** Fixed (seed MIR lowering)
**Symptom:** under the JIT every https fetch in the browser failed with
`h1: TLS read failed or timed out for example.com:443`; interpreted, it worked.

## Root cause

`h1_client.spl` reads the response through `read_tls_response_bytes`, which
returns `Pair<[u8], bool>`, then computes:

```
val unclean_eof = read.second or closed.is_err()
```

`Pair<K, V>.second` is a type-parameter field, lowered as `ANY`: a tagged
`RuntimeValue`. MIR `Branch`, the `and`/`or` short-circuit and `not` test the
raw machine word, and a tagged `false` (and `nil`) is a non-zero word. So
`false or false` was `true`, and a complete 930-byte example.com response was
refused as an unclean EOF. Instrumented under JIT:

```
second=false closed_err=false len=930 selfdelim=false unclean=true
```

The low-level TLS externs were never the problem: a direct
connect/write/read/close probe returned the same 930 bytes on both lanes.

Minimal repro (JIT prints `TAKEN`, interpreter does not):

```
val a = Pair(1, false)
if a.second:
    print "TAKEN"
```

## Fix

`MirLowerer::lower_condition_expr` (`mir/lower/lowering_core.rs`) lowers a
condition and, when its type is `ANY`, decodes it through `rt_value_truthy` —
the interpreter's truthiness (`false`, `nil`, `0`, `0.0` falsy; heap objects
truthy). Used by `if`/`elif`, `while`, `assert`, `assume`, the if-expression,
both sides of `and`/`or` (also the coverage variant), and `not`. Typed `bool`
conditions are unchanged (no extra call).

## Evidence

- Cargo: `mir::lower::tests::branch_coverage::types::any_condition_decodes_truthiness`
  (each condition form emits `rt_value_truthy`; a typed bool does not).
- Specs (semantics on both lanes): `test/01_unit/compiler/generic_bool_field_condition_spec.spl`
  (the exact Pair shape) and `test/01_unit/compiler/any_value_condition_spec.spl`
  (generalization: `any` params, untyped `list` elements, nil/0/text). Note:
  `it` bodies currently execute on the interpreter even under `run`, so these
  pin the semantics; the JIT lowering is pinned by the cargo test and the
  probe below.
- JIT probe, before/after: `count_false=111` -> `1000` for
  `if p.second` / `or` / `and` / `not` on `Pair(1, false)`.

## Second root cause on the same path: `rt_slice` ignored packed arrays

With the condition fixed, the JIT fetch got further and failed with
`h1: invalid HTTP version in status line: '?D ...'`. The 931 response bytes
were intact up to `parse_http_response_bytes`; `raw.slice(0, i)` in
`split_header_body_bytes` returned garbage. A fetched `[u8]` is a BYTE-PACKED
`RuntimeArray`, and `rt_slice` (`runtime/src/value/collections.rs`) copied
`(*arr).as_slice()`, which reads the buffer as `len` 8-byte tagged slots:
every element was 8 ASCII bytes glued into a word (`0x4f203430202c6e75` =
"un, 04 O"), and the read ran 8x past the end of the byte buffer
(out-of-bounds read). Small literal arrays are not packed, which is why
isolated probes passed.

Fix: `rt_slice` keeps the source layout for byte-packed and u64-packed arrays
(same approach `rt_array_concat` already took). Cargo:
`value::collection_tests::test_slice_packed_arrays_keep_elements`.

**Open class (not fixed here):** `as_slice()` has ~113 call sites in the
runtime; any that do not check `is_byte_packed()`/`is_u64_packed()` first have
the same defect for packed arrays. Owner: whoever owns the packed-array
(`Value::Array`) layout work. Repro shape: build a `[u8]` from a runtime text
(`text_to_bytes` of a fetched chunk) and call the method under the JIT.

## Also observed, not fixed

- `"x" * 4000` evaluates to length `-1` under the JIT (4000 interpreted).
- `any_value as i64` (`Cast` ANY -> I64) does not unbox: printing
  `parts.first[0] as i64` on a `Pair<[u8], _>` field gave the raw tagged word.
