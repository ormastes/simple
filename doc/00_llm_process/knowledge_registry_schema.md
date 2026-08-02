# Knowledge Registry Schema

`knowledge_registry.sdn` is the canonical, versioned routing inventory. A feature
route has one exact `feature_id`, group base, and optional expert overlay. A
layer route has a normalized repository-relative source prefix, layer base,
optional expert overlay, and architecture profile.

Selection is fail-closed: exact feature match, then longest path-prefix match
for every planned or changed source path. Equal-length competing layer groups,
missing routes, duplicate feature IDs, and empty path sets are errors. Results
are deduplicated and lexically ordered before the receipt is written.

`src/os/kernel/**` and `src/os/drivers/**` always require `mdsoc_only`. This is a
hard selector invariant; feature metadata cannot enable ECS or MDSOC+ there.
Receipts record registry version, feature, selected knowledge paths, each source
path and matched prefix, and architecture profile.
