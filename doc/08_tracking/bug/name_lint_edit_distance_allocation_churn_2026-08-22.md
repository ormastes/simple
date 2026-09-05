# NAME001 bounded edit-distance allocation churn

## Status

Resolved structurally with a three-row fixed-band implementation. Static audit
only; executable measurement was intentionally not run under the user's
no-verify instruction.

## Evidence

For every non-exact child/inherited method-name pair, the current bounded
Damerau-Levenshtein helper allocates initial rows, one new row per candidate
byte, and one-byte substring values per matrix cell. Although the accepted
distance is only one or two and length-difference rejection is early, the
implementation still performs `O(K^2)` cell work and allocation traffic for
same-length names of length `K`. Candidate iteration itself must remain ordered
because the first qualifying parent name is embedded in NAME001.

## Correction

The helper now visits only columns `i-limit` through `i+limit`, compares
`byte_at` values, and rotates three scalar row IDs over one flat buffer of
`3 * (2 * limit + 1)` integers. Stale cells are excluded by each row's explicit
logical start/end, so reuse does not require clearing or reallocating rows.
Adjacent transposition still reads row `i-2`; insertion, deletion,
substitution, transposition, limit-two, negative-boundary, Unicode byte, and
first inherited-match contracts are mirrored in both lint specs.

For the NAME001 limits one and two, work is `O(K * limit)` and live/allocated
matrix storage is `O(limit)` per comparison, replacing `O(K^2)` cells,
one-byte substring temporaries, and cumulative row allocation. Exact runtime
and allocation measurements remain unavailable under the no-verify direction.
