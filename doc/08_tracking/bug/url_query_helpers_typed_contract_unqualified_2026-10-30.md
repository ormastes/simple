# URL query helper types remain unqualified

Status: **OPEN**. The production helpers now declare their pair contract:
`parse_query_string` returns `[(text, text)]`, `parse_query_param` returns
`(text, text)`, and `build_query_string` accepts `[(text, text)]`. The function
algorithms were not changed.

The prior bare `list` and `tuple` declarations erased the element contract to
`Array(Any)` and an empty tuple type in HIR. The old URL utility SSpec copied
the implementations locally, so it did not compile or execute the production
query helpers. A new SSpec and standalone fixture import the production module
directly.

## Bounded native evidence

The final fixture compiled with exit 0 using the attempt17 admitted producer
(`9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`) and its
matching runtime capsule. The process-tree watchdog recorded exit 0,
quiescence, and peak RSS 2,377,108 KiB under the 8,388,608 KiB cap. The frozen
SCV snapshot hashes for the changed URL module and fixture match the worktree.

The one allowed execution exited 1 with:

```text
URL_QUERY_CONTRACT_FAIL|checks=-7
```

Fieldwise checks for empty parse/build, ordered multiple pairs, flag pairs,
empty values, splitting at the first `=`, and UTF-8/plus decoding passed. The
exact encoded-builder output check failed. The round-trip group was therefore
not executed. SSpec execution was not run.

An earlier aggregate-equality diagnostic returned `checks=-2` for the
multiple-pairs comparison. The final fieldwise checks passed every key/value
and length in that group. The reason for that aggregate-versus-fieldwise
difference is unknown; it does not establish a compiler equality defect or a
URL library defect. The final encoded output was not captured, so its mismatch
is also unresolved. Do not treat these type annotations or native results as
release qualification.

Full logs, executable, source hashes, and watchdog receipts are preserved in
the ignored worktree directory `build/url-query-contract-cycle5/` and
`build/url-query-contract-cycle6/`. The structured receipt is
[`url_query_helpers_typed_contract_unqualified_2026-10-30.sdn`](url_query_helpers_typed_contract_unqualified_2026-10-30.sdn).
