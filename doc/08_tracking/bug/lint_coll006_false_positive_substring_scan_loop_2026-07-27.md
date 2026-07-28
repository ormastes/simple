# COLL006 "string concat in loop" fires on loops with no string concatenation

**Status:** Fixed 2026-07-28 (working copy) — see .spipe/lint_coll006/state.md
**Found by:** lane URLPARSE, 2026-07-27
**Component:** `bin/simple lint` — rule `COLL006`

## Symptom

`COLL006: string concat in loop (O(n^2))` is reported for functions whose loop
body contains **no string concatenation at all** — only `text.substring()` reads
in a `while`.

## Reproduction

`bin/simple lint src/lib/nogc_sync_mut/http_client/types.spl` reports COLL006 at
three functions that never build a string:

- `_url_parse_port` — loop body is `val c = s.substring(i, i + 1)`,
  `val d = "0123456789".index_of(c)`, `acc = acc * 10 + d`. The only `+` is
  integer arithmetic.
- `_url_valid_host` — loop body is `val c = host.substring(i, i + 1)` followed
  by a chain of `==` comparisons. There is no `+` in the function at all.
- `_url_valid_ipv6` — same shape, no `+` in the function at all.

A fourth hit lands on `parse_url` itself, whose only text `+` is
`host = "[" + inner.to_lower() + "]"` — a single concatenation *outside* any
loop.

## Expected

COLL006 should fire only when a text-typed variable is reassigned from a
concatenation whose left operand is that same variable, and that assignment is
inside a loop (`out = out + c`). Read-only `substring` scans and integer
accumulation must not trigger it.

## Likely cause

The rule appears to be attributed at function granularity: presence of *a* loop
plus presence of *a* text operation anywhere in the function is enough. The
reported line number is the `fn` line, not the offending statement — which is
itself a symptom of the coarse attribution.

## Impact

Character-scan helpers (the standard way to write a validator over `text` in
pure Simple) cannot pass lint without being rewritten into a shape that is
neither shorter nor faster. This is exactly the "workaround silently
normalized" pattern the project rules forbid.

## Workaround applied

None — the code is written in the correct shape and the lint hits are left
in place, documented here. The one *genuine* COLL006 in the same file
(`_url_strip_tabs` building a result with `out = out + c`) was rewritten as
`split(sep).join("")`, which is a real improvement.

## Notes

Three pre-existing COLL006 hits in the same file (`parse_query_string`,
`build_query_string`, `remove_query_param`/`add_query_param`) are genuine and
predate this lane.
