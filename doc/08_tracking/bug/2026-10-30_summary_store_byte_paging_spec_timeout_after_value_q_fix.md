# summary_store_byte_paging_spec times out (>900s) once `value?` parses

- Status: OPEN 2026-10-30
- Component: interpreter/seed runtime performance, or spec sizing
- Spec: `test/01_unit/compiler/cache/summary_store_byte_paging_spec.spl`
- Found by: verification of PR #5478 (seed parser: trailing `?` glued onto member names)

## Symptom

Before #5478 the spec failed fast: 0/3, each example with
`class SummaryLookupV1 has no field named value?`. After #5478 that parse error
is gone, and the run is killed at 900s. The output ends with
`Results: 0 total, 0 passed, 0 failed` and no example verdicts.

Measured with a debug seed built from release/1.0.0 plus #5478 (macOS,
`src/compiler_rust/target/debug/simple test <spec>`).

## Likely cause (unconfirmed)

The first example walks the rendered summary once for each `limit` in
`[1, 3, 65, 65536]`. Each step makes a `facade.read` and a `facade.page`
call, runs 10 expectations, and computes about 10 `sha256_text` hashes:
`paging_auth()` twice at 4 each, `paging_token` once, and the page digest once.
With `limit = 1` that is a full round trip per byte. The parse error used to hide this cost.
It has not been profiled. It could be ordinary interpreter slowness, or
superlinear work in `read`/`page`, such as re-rendering the summary or
re-slicing the whole text on every call.

## Next steps

1. Time a single `read`/`page` call against summary size to tell linear from
   superlinear cost.
2. If the per-call cost is superlinear, fix the summary store. If it is linear
   and only the interpreter is slow, record the cost and run the
   spec on the native/compiled lane. Do not weaken the byte-boundary coverage.

Related, separate defect: `summary_store_v1_spec` example 1 still fails after
#5478 with `method to_bytes not found on type str`.
