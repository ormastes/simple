# URL query helper native qualification

Status: **Native fixture passed; full SSpec and CLI qualification remain unrun.**

The production query APIs retain concrete pair contracts:
`parse_query_string` returns `[(text, text)]`, `parse_query_param` returns
`(text, text)`, and `build_query_string` accepts `[(text, text)]`. The builder
uses explicitly typed tuple/text locals and joins the accumulated parts with
`parts.join("&")`.

## Final bounded native evidence

- Rebased PR head: `c7a8621c417`.
- Producer: admitted Stage 2 `simple`, SHA-256
  `9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`, with
  its matching frozen runtime capsule.
- Exact source qualification used URL SHA-256
  `56626fd50fecc434fa9bdea4b5cfc49072fa5dae156ce8205d36c215c81c36ad`, shared
  checks SHA-256
  `0fe3089a5b2efffaf3b396344b40bdd1ff0a8bec0f9042f08fc12820926ff97d`, and
  fixture main SHA-256
  `155ce51a9e3d18e99ddc07a67917dbe1447881b404c2710369b257ac68c8ac28`.
- Native build exit status 0; watchdog quiescent, peak 2,570,780 KiB under the
  8,388,608 KiB cap.
- The executable ran once and printed `URL_QUERY_CONTRACT_PASS|checks=8`.
  The exact encoded string and ordered duplicate-key round-trip assertions
  passed.
- The SSpec and full compiler/test suites were not run.

## Diagnostic history and remaining scope

The first native fixture attempt failed at the builder assertion (`checks=-7`)
with the original reversed join receiver. Isolated native diagnostics showed
that direct ASCII and UTF-8 encoders were correct; implicit tuple-array field
locals could become pointer-like numeric strings. Explicit local types and the
array-receiver join produced the expected builder value and 8/8 checks. This
qualifies the URL call boundary on the admitted producer; it does not establish
a general tuple inference fix.

The initial failed logs and receipts remain in the original worktree's
`build/url-query-contract-cycle6/`. Detailed type-provenance evidence and the
open compiler follow-up are recorded in
[`native_tuple_array_local_text_provenance_2026-10-30.md`](native_tuple_array_local_text_provenance_2026-10-30.md).
