# aspect_match_shard_v1: unknown atom form yields an empty complete shard (fail-open)

Found by the AW-0b Fable review of `test/01_unit/compiler/aop/aspect_match_shard_v1_spec.spl`.

## Defect

`src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl`, `_node_matches`
(tail, L356): a `supported` selector whose atom has a `form` other than
`exact`, `prefix`, `attr`, `within` or `within_tree` evaluates to `false` for
every join point. `pointcut_match_shard_compute_v1` then returns
`sorted_matching_ids = []` with `complete = true`, and
`pointcut_match_cache_acquire_v1` admits it to the cache. An unrecognised form
is therefore reported as "matches nothing, proven" instead of failing closed.

The parser never produces such a form, so it is latent. AW-3 builds selectors
outside the parser, which makes it reachable. The spec pins the current
behaviour (`a hand-built selector node with an unknown form matches nothing`)
and must be flipped when this is fixed.

Expected: an unknown atom form makes the selector unsupported (or the shard
`complete = false`), so it is never cached.

## Redundant conditions (same follow-up product change)

- L400: `aop_digest_known_v1(f.facts_key)` in `cacheable` is implied by the
  facts-key check in `pointcut_match_key_v1` (an empty key is handled at L403).
- L403 and L410: the argument `key != ""` passed to
  `_pointcut_match_shard_compute_known_v2` is constant at both sites (false at
  L403, which is only reached when the key is empty; true at L410).

Remove these in a follow-up product change; the spec covers them as written and
needs no change except the unknown-form expectation above.
