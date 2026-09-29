# Ordered-key erased ABI retains legacy text, float and scalar limits

Status: follow-up; the bootstrap provider fix preserves existing core-C behavior.

Affected boundary: `spl_ordered_key_cmp(i64, i64)` in the core-C and hosted Rust runtimes.

- Text compares bytes through the first NUL. Distinct text keys `a\0z` and
  `a\0b` compare equal. A future content-length contract must change both owners
  together and verify OrderedMap insert/lookup behavior for embedded NUL.
- Boxed NaN compares equal to every supported boxed float because neither `<`
  nor `>` succeeds. This is not a total order. A future change must select and
  verify a consistent rejection or total-order policy in both owners.
- Erased raw scalar words overlap value tags. Raw 10 stays integer 10, while
  a word with low tag zero is decoded as a tagged signed immediate. Tagged nil
  and booleans currently retain raw-word ordering (3, 11, 19). A representation
  change needs explicit type information, coordinated callers, and ABI tests;
  inferring floats or dereferencing apparent heap tags would be unsafe.

The focused Rust provider tests record these existing behaviors alongside safe
registered-heap classification, supported numeric widths, and unsupported
aggregate rejection. No semantic widening is included in the bootstrap fix.
