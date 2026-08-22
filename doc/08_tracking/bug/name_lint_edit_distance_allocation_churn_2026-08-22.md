# NAME001 bounded edit-distance allocation churn

## Status

Open after the class, inheritance, and accessor-group indexing tranche. Static
audit only; executable measurement was intentionally not run under the user's
no-verify instruction.

## Evidence

For every non-exact child/inherited method-name pair, the current bounded
Damerau-Levenshtein helper allocates initial rows, one new row per candidate
byte, and one-byte substring values per matrix cell. Although the accepted
distance is only one or two and length-difference rejection is early, the
implementation still performs `O(K^2)` cell work and allocation traffic for
same-length names of length `K`. Candidate iteration itself must remain ordered
because the first qualifying parent name is embedded in NAME001.

## Required correction

- Restrict computation to the distance band needed by limit one or two.
- Compare byte/code-unit values without allocating one-byte substrings.
- Reuse bounded row storage without triggering COW detaches.
- Preserve adjacent-transposition behavior and the exact first-match order.
- Add insertion, deletion, substitution, transposition, Unicode/byte-contract,
  limit-two, and negative-boundary fixtures plus a scaling allocation contract.
