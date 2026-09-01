# Aspect-pack per-loader registry

This manual covers the Pure Simple aspect-pack registry’s externally visible
behavior after replacing process-global parallel arrays with one path-indexed
dictionary per loader.

## Covered behavior

- A duplicate path in one loader fails with the exact established diagnostic.
- Unregistering a path permits a later registration and the replacement bytes
  are the bytes loaded through the catalog.
- Two loaders may register the same path with distinct payloads without
  observing each other’s entries.
- Unregistering one loader’s path does not affect another loader.

## Performance contract

Dictionary membership, insertion, exact-path lookup, and registry removal are
O(1) average with respect to registered pack count. Registration and lookup
retain the reference-backed `[u8]` payload; they do not copy payload bytes.
Loader creation allocates one empty dictionary. Dictionary metadata may grow
on insertion or be replaced on removal. Existing binding and activation scans
remain unchanged and are outside the pack-registry lookup cost.

## Verification status

Not executed in this change set, per the explicit no-verification instruction.
