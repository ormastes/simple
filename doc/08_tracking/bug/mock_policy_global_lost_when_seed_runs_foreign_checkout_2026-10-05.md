# `std.spec.mock` policy global write is lost when a seed runs a different checkout (2026-10-05)

**Status:** OPEN.

`test/01_unit/lib/common/mock_spec.spl` › "matches custom patterns" fails, with
`expected false to equal true`, whenever a seed binary runs against a checkout
other than the one it was built from. It passes 41/41 when each binary runs
in its own tree:

| binary built from | run in | result |
|---|---|---|
| tree A | tree A | 41/41 |
| tree A | tree B | 40/41 |
| tree B | tree B | 41/41 |
| tree B | tree A | 40/41 |

Minimal reproduction (interpreter mode):

```
mock_policy_init_with_patterns(["*.cache.*"])   # assigns module global _mock_policy_patterns
mock_policy_matches_any_pattern("app.cache.redis")   # reads it -> false in a foreign tree
```

Calling `mock_policy_pattern_matches` directly returns `true` in every case.
So the write to the module global is not seen by the next function. This
suggests the module is loaded twice under two path keys, once from the
binary's built-in source root and once from the working tree, with one
global store per copy. Found during the #2526 spec sweep.

**Unblock condition:** find which module path key differs when the seed's
compile-time source root is not the working tree, and resolve both
spellings to one module instance.
