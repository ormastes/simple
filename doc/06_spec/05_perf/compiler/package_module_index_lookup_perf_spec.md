<!-- codex-design -->
# Package module index lookup performance

The production persistent package/module index is sorted by `module_identity`.
Warm admission, dependency validation, invalidation, and SCC scheduling resolve
many module identities from that index. The implementation therefore uses
binary search rather than a full scan for each lookup.

The executable SPipe specification constructs a 4,096-module index, verifies
first, middle, last, and absent identities, then performs 16,384 deterministic
warm lookups. It requires completion within five seconds and writes the actual
elapsed time to:

```text
build/test-artifacts/05_perf/compiler/package_module_index_lookup/receipt.txt
```

This is focused algorithmic evidence. Product-level clean, warm no-op, and
private-body build latency still require a producer-authenticated native
compiler and runtime archive set.
