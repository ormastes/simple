# JIT `write_span` out of range ran silently; interpreter raised (2026-10-05)

**Status:** FIXED on branch `work/engine2d-mem`.

## Defect

`arr.write_span(src, dst_off, src_off, count)` with an out-of-range span:

| lane | before | after |
|---|---|---|
| interpreter | `error: semantic: write_span out of range: dst_off=2 src_off=0 count=5 dst_len=3 src_len=5`, exit 1 | unchanged |
| JIT (`simple run`, default) | no diagnostic, program continued, exit 0 | same diagnostic, exit 1 |

The compiled lanes call `rt_array_write_span`, which returned a tagged `-1`
for out-of-range spans and for a non-array source. No call site checks the
returned value, so the bad call was silently dropped and the program kept going.

## Fix

- Seed runtime: `src/compiler_rust/runtime/src/value/collections.rs`.
  `rt_array_write_span` now prints the interpreter's exact message and exits
  with status 1. The bounds rule lives in `write_span_range_check`, which uses
  `checked_add` so an overflowing offset is reported instead of wrapping.
- C runtime twin: `src/runtime/runtime_native.c` `rt_array_write_span`. Same
  message, same exit status.
- An invalid *destination* handle still returns `-1`. The compiler only emits
  this call for an array receiver, so a non-array destination is ABI misuse
  rather than a program error.

## Evidence

- Rust tests: `write_span_range_tests::{in_range_spans_pass,
  out_of_range_matches_the_interpreter_message,
  overflowing_offsets_are_reported_not_wrapped}`.
- Fixture `test/fixtures/compiler/write_span_lane_parity_probe.spl` (field fill, aliased field,
  self-overlap, nested place, `count = 0`, out of range). Under the JIT its
  output is byte-identical to the interpreter's, including the error and exit 1.
