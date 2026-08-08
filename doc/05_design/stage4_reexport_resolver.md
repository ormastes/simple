<!-- codex-design -->
# Stage4 re-export resolver detail design

`find_reexport_source` forms a root key from `facade_name` and `wanted`.
It first reads the cache owned by its `ModuleSurfacesByName` snapshot. On a
miss it performs the existing bounded DFS using only `reexport_active` to
break path cycles, then records the completed result in the snapshot cache.

The cache records both misses and positives. A DFS early return caused by an
active path is not inserted as a completed answer. Tests create two lowerings
that share a snapshot, verify cache reuse, then create a new snapshot and
verify lookup starts uncached.
