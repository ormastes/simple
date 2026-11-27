# `.to_int()` on an erased receiver lowered as a text parse

- **Date:** 2026-11-23
- **Status:** fixed (branch `work/compiler-erased-elem-to-i64-20261123`)
- **Area:** MIR lowering, `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (erased-receiver text-builtin arm, `erased_text_shape`)
- **Follow-up of:** PR #10920 / `phase2_byte_at_to_i64_lowered_as_text_parse_2026-11-23.md` (reviewer note)

## Problem

An untyped (erased) receiver whose method name is in the primitive text table is
admitted to the erased-receiver text arm. `to_i64` already had an escape: when the
receiver local is a runtime (tagged) value it lowers to `rt_any_to_int`, the tagged
conversion owner (parses text, unboxes ints, truncates floats). Its alias `to_int`
had no such escape, so on the Phase 1 seed:

| source | callees before | after |
|---|---|---|
| `fn f(xs, i: i64): xs[i].to_int()` | `rt_index_get, rt_string_new, rt_string_to_int_lenient` | `rt_index_get, rt_any_to_int` |
| `val x = xs[i]; x.to_int()` (xs untyped) | `... rt_string_to_int_lenient` | `rt_any_to_int` |
| `fn f(x): x.to_int()` | `... rt_string_to_int_lenient` | `rt_any_to_int` |

A numeric element was boxed as text and parsed -> wrong value (0).

## Root cause

`to_int` and `to_i64` are one text-table entry (both map to
`rt_string_to_int_lenient`), but the runtime-dispatch escape tested only
`method == "to_i64"`.

## What was NOT broken (probe evidence)

Known element types already propagate and stay numeric:
`xs: [i64]` `xs[i].to_i64()/.to_int()` -> `rt_value_as_int_wide`; `[u8]` ->
`rt_bytes_u8_at`; `Dict<text, i64>` value; `xs.map(\x: x.to_int())` and
`xs.map(&:to_int)` on `[i64]`; `xs.get(i).to_i64()` on `[i64]` -> `rt_any_to_int`.
No element-type propagation change was needed.

## Fix

Extend the escape to `method == "to_i64" or method == "to_int"` (same gate:
zero args, erased receiver, runtime-value local). `parse_int`/`parse_i64` are not
included: they return `Option`, a different shape.

## Remaining gaps (named, not fixed here)

- **`x: any` parameter:** `x.to_int()` on a declared `any` param still lowers as
  a text parse (probed before the fix; `to_i64` not probed but takes the same
  gate) — the param is not a runtime-value local, and
  legacy `Any` locals may hold raw words, so `rt_any_to_int` is not safe there
  without a tag proof.
- **`.get(i)` on a fully untyped receiver** (`fn f(xs, i): xs.get(i).to_int()`)
  lowers `get` through a text path (`rt_string_data`, `rt_panic`) before any
  conversion runs; `.map(...)` on an untyped receiver likewise emits `rt_panic`.
- **Runtime divergence:** `rt_any_to_int` -> `rt_string_to_int`, lenient strtoll in
  the C runtime but strict `parse::<i64>()` in the Rust runtime
  (`"4x2"`: 4 vs 0). Pre-existing on the `to_i64` path; now also reached by `to_int`.
- `to_float` / float-parse aliases remain in `erased_text_shape` with the analogous
  hazard for erased float elements.

## Call-site census (src/)

`grep -rnE '\]\.to_int\(\)|\.get\([^)]*\)\.to_i(nt|64)\(\)'` -> 252 hits; nearly all
are `[text]` split results (`parts[i]`, `fields[i]`, `args[i]`), genuine text parses.
Numeric-element sites checked are typed and safe: `src/lib/common/bytes/ints.spl`
and `checksum.spl` (`span: ByteSpan`, `.get(i).to_i64()`),
`src/app/build/scheduler/parent_artifact_export.spl:75-114` (`bytes: [u8]`).

## Verification

Phase 1 seed interpreter, `simple.exe test`:
- Repro + generalization spec `test/01_unit/compiler/50.mir/erased_element_to_int_dispatch_spec.spl`:
  old code 5/8 (3 `to_int` cases RED), fixed 8/8. Controls (`s: text`, `xs: [text]`)
  keep `rt_string_to_int_lenient` and do not reach `rt_any_to_int`.
- Adjacent `test/01_unit/compiler/50.mir/byte_at_to_i64_numeric_receiver_spec.spl`: 5/5.
