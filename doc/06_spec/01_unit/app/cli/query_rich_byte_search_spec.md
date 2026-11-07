# Rich-query byte-offset search

Source: `test/01_unit/app/cli/query_rich_byte_search_spec.spl`.
Requirement: REQ-CLI-QUERY-RICH-BYTE-SEARCH. Authored mirror; docgen and all
four examples NOT_RUN. Uses actual `_find_in_line` / `_find_in_line_from`;
no copied search implementation, fabricated result, or raw provider workaround.

Each scenario prepares real text, invokes the production owner, checks the
observed contract, and checks the neighboring failure case.

| Scenario | Main contract | Neighboring controls |
|---|---|---|
| Unicode search | `A한éZé` finds é at byte 4 then 7; `é한😀` finds emoji at 5 | Exact start, mid-code-point start, byte-end absence |
| Absent / longer needle | 0 and -1 remain the respective absent sentinels | Real match at offset 0 keeps the intentionally ambiguous first API |
| Empty / starts | Negative starts clamp to 0; empty needle at `é` byte-end 2 returns 2 | Beyond end, empty carrier, nonempty needle at end |
| NUL carrier | `é\0한\0` finds NUL at 2 then 6; a NUL-prefixed needle matches at 2 | Longer absent NUL needle and empty needle at byte-end 7 |

The NUL carrier and NUL-prefixed needles are created with the production
`bytes_to_text` owner from explicit UTF-8 bytes, avoiding C-string literal
promotion truncation. Setup asserts the 7-byte carrier, both zero bytes,
the complete following Korean code point, and needle byte lengths before search.

These oracles use literal UTF-8 byte positions, independent of `text.len()`
semantics. Original code may pass on an engine where len still returns bytes;
the regression appears when len returns code points (selected design #7425/C1).
No before/after runtime failure or native qualification is claimed.

The production fix obtains byte counts through the existing exported `str_len`
owner and retains byte substring/byte_at comparisons, avoiding dependence on
the pending MIR byte_len method rollout. Complexity remains the existing linear
scan over candidate byte positions with per-needle comparison; caching lengths
avoids repeating character scans. No sentinel or Unicode normalization policy
is changed.
