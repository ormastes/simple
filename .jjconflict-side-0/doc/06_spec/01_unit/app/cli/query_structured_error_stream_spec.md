# Query Structured Error Streaming Specification

Source: `test/01_unit/app/cli/query_structured_error_stream_spec.spl`

Evidence status: authored but not executed under the user-requested no-verify
override.

## Scenario: structured metadata preserves legacy ordering

The executable fixture combines whitespace, consecutive separators, two
`RELATED` items (including a multibyte payload), an unknown segment, and two
`HELP` items. It requires ordered related payloads and last-help-wins behavior.
It also pins no-metadata passthrough
and empty related/help payloads, then proves the compatibility wrapper equals the
canonical result.

## Scenario: one cursor parser owns all structured splitting

The structural fixture bounds the canonical body, pins its two separator-search
sites and monotonic cursor, and requires direct related-item append. It rejects
split arrays, a retained metadata suffix, and functional push reassignment.
`query_diagnostics` is limited to a search/slice/loop-free compatibility wrapper,
and `query_check` must call the canonical parser without a local implementation.

For N diagnostic bytes and fixed three-byte separators, parsing is O(N).
Retained result storage is O(C + R + K) for copied core bytes C, metadata payload
bytes R, and K RELATED handles. Peak parser storage adds O(max segment), and is
O(N) worst case. Each segment still creates one bounded slice for trimming; the
removed full suffix and all-segments array no longer overlap those results. No
runtime allocation, timing, or RSS measurement was performed.
