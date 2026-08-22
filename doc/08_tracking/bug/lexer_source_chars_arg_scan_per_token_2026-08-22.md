# Lexer passed `source_chars` by argument: O(file) per token under the seed (2026-08-22)

## Symptom

`src/compiler/hir/generated/hir_codec.spl` (6107 lines, 224 KB, trivial
`if tag == N: return X` bodies) took 19.8 min to parse in the stage1 driver
(`[build] parse 407/687 step 1/6 dt=1186509ms`). Bare-parse probe on the
pinned seed `simple.1ffdfb58baf` (`SIMPLE_EXECUTION_MODE=interpret`, load ~50):
824 lines 44 s, 1600 lines 106 s — 2.4x for 1.9x the lines, ~53 ms per line.
Same class as `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.

## Mechanism (one of two; the other is the seed-side record below)

`SIMPLE_PERF_COUNTERS=1` on a 50-function fixture: `VT_ARRAY_ELEMS_SCANNED`
465,504 — 27x the 10-function value for 5x the functions. A new attribution
trace (`SIMPLE_PERF_COUNTERS_TRACE=<min_len>`, seed) named it:
`vt_arg_scan name=chars len=1882` x 247 — one per token.

`core_token_text_matches(chars: [text], start, end, value)` in
`src/compiler/10.frontend/core/lexer_struct.spl` took the lexer's whole
`source_chars` array (one entry per source character) as an argument, from
three per-token call sites (`char_slice` intern hit, keyword check, suffix
check). The seed's argument binder scans every element of every array
argument for value-type structs (`copy_value_type_in_place`,
`interpreter_call/core/arg_binding.rs`), so each token cost O(file). For
hir_codec that is ~40k tokens x 224k chars = 9e9 element visits.

## Fix

The helper is now a method `chars_match(start, end, value)` on `CoreLexer`
reading `self.source_chars` in place: O(span) per call, byte-identical
result. `VT_ARRAY_ELEMS_SCANNED` on the 50-fn fixture: 465,504 -> 650.

## Sibling defect (seed side)

Even with this fix the parse stays quadratic on the deployed seed because every
`global_array.push(x)` inside a function deep-copies the array once per frame
and the parser pushes ~70 flat-AST pools per node. That is the larger term for
big files and is fixed in the Rust seed separately:
`doc/08_tracking/bug/seed_global_array_push_cow_per_frame_2026-08-22.md`.
Pinned by `test/01_unit/compiler/frontend/lexer_source_chars_not_passed_per_token_spec.spl`
(source-shape, fails pre-fix; the seed half is pinned by the Rust test
`src/compiler_rust/compiler/tests/interpreter_global_array_push_in_place.rs`).
A 2x-size timing ratio was tried and rejected: at unit-spec sizes (60-120
functions) the linear interpreter floor (~30 ms per function) hides both
quadratic terms, and the seed half cannot go green until a redeploy anyway.
