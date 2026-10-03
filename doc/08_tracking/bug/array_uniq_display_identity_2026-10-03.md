# Dynamic distinct values must not use display text as identity

The sync and async `array_uniq` implementations used `"{item}"` as a dictionary
key. Unequal values such as integer `1` and text `"1"` could therefore collapse.
The correction retains the first value under actual equality and includes
mixed-type, order, repeated-value and signed-zero regression cases.

The universal `[Any]` entrypoint has no established hash/equality contract.
It now explicitly uses an equality-only O(n*d) fallback, where d is the number
of distinct values, with O(d) result storage. This is a correctness repair and
a known cost tradeoff, not the indexed complexity completion required by
REQ-004. A future fast path must prove compatible hashing for its supported
types and retain equality checks for collisions; formatting is never that proof.

The eight sync/async scenarios are authored but unexecuted. No timing or engine
parity result is claimed. Explicit hashed grouping has a separate caller-owned
hash/equality contract and does not silently authorize this dynamic entrypoint.
