# Numeric join engine fixtures

Authored manual for the paired
`test/fixtures/engine_differential/collection_req001_numeric_join_sync.spl`
and `collection_req001_numeric_join_async.spl` programs. Both call their actual
production DataFrame merge implementation and have exact sibling output oracles.
They are unexecuted and do not certify REQ-001 or engine parity.

Each side contains positive zero, negative zero, NaN, two equal keys and a
masked key. Independent row-ID tables specify every expected output row:

| Operation | Required result |
|---|---|
| Input checks | NaN compares unequal to itself; negative zero has its IEEE sign bit. |
| Inner merge | Eight rows; signed zeros match and equal-key duplicates retain left-major/right-insertion order. |
| Outer merge | Twelve rows; NaN and masked keys never match, including each other; unmatched right rows follow left rows. |
| Outer key payloads | NaNs remain present NaNs; missing-key rows retain their masks. |
| Right merge | Ten rows; right-major order with left duplicates in insertion order and explicit missing-side masks. |

The row comparison helper inspects production outputs against literal tables;
it does not implement a second join. Mismatches return nonzero without the
success marker. Select both fixtures with `DIFF_FILTER=collection_req001_numeric_join`
in the existing differential runner and require `DIFF_CERTIFY=1` for certification.
Both facade families require execution; the async-family fixture does not test
scheduling. First/last/unique policies and measured complexity remain separate
acceptance obligations.
