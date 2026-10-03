# Dynamic distinct identity

Authored companion to `test/01_unit/lib/nogc_async_mut/array_uniq_identity_spec.spl`.
Four scenarios assert mixed integer/text identity, mixed boolean/text identity,
first-occurrence ordering with equal duplicates/empty input, and signed-zero
numeric equality. They call the real `array_uniq` implementation.

Arbitrary dynamic values use a documented O(n*d) equality-only fallback.
The tests establish neither an indexed complexity claim nor cross-engine
execution evidence. All four remain unexecuted pending an admitted runner.
