# Map.insert_if_absent fails dispatch as "method not found on type dict" (2026-09-15)

- File: `src/lib/nogc_sync_mut/src/map.spl:325` — `me insert_if_absent(self, key: K, value: V) -> bool`
  exists; the async facade `src/lib/nogc_async_mut/src/map.spl` re-exports it.
- Observed: `test/01_unit/lib/nogc_async_mut/map_insert_if_absent_spec.spl` (and
  `collections/src_collections_facade_spec.spl`,
  `src/collections/src_collections_facade_spec.spl`) fail with
  `semantic: method 'insert_if_absent' not found on type 'dict' (receiver value: {})`
  even when importing `std.nogc_sync_mut.src.map.{Map}` directly. Sibling
  `test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl` using `Map.new()` + other
  methods passes 6/6, so construction works; this one method's dispatch does not.
- Note the signature oddity: `me` method with an explicit `self` parameter.
- Unblock condition: make `insert_if_absent` dispatchable on `Map` receivers (likely the
  explicit-`self` `me` signature or the facade re-export chain), then the three specs
  should pass unchanged.
