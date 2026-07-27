# BUG: every container off the same base image was handed the SAME COW writable layer id

- **Status:** FIXED 2026-07-27 (lane CESC)
- **Severity:** HIGH — cross-container data escape in any real COW backend
- **Component:** `src/os/services/container/container_manager.spl` (`sys_create`)
- **Found by:** `test/01_unit/os/services/container/container_escape_suite_spec.spl`
- **Related:** master plan §6.4 (image/volume store)

## Summary

`sys_create` derived the writable-layer id purely from the base image digest:

```
val cow = image_digest + ":cow"
```

The base digest is CONTENT-ADDRESSED, so it is deliberately identical for every
container started from the same image — which made the writable layer id
identical too. Two containers sharing a base were registered against one and the
same COW layer name.

The in-memory model masks the impact: `LayerStore` keys snapshots by `owner`, so
`snapshot_write` / `snapshot_used` stayed isolated in this test build. The bug
is in the NAME that a real overlay/COW backend would mount. Two containers
mounting the same upper layer means container A reads and writes container B's
files — a full cross-container data escape, and the exact opposite of the
isolation the §6.4 model claims.

## Minimal repro (pre-fix)

```
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:shared", ...)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:shared", ...)

# PRE-FIX observed:
#   w.snapshot_layer_of(a) == "sha256:shared:cow"
#   w.snapshot_layer_of(b) == "sha256:shared:cow"   <-- identical
```

## Fix

The container id disambiguates the writable layer; the base digest stays in the
name so the parent chain is still readable:

```
val cow = image_digest + ":cow:" + "{cid}"
```

## Callers updated

`test/01_unit/os/services/container/container_monitor_gc_spec.spl` asserted the
old layer id literally in two places (`sha256:base:cow:rb`,
`sha256:ghost:cow`); both now assert the per-container form
(`sha256:base:cow:1:rb`, `sha256:ghost:cow:1`). No production caller parses the
layer id.

## Follow-up

`ContainerIsolation.lean` models namespace and capability isolation but not
STORAGE isolation. A theorem stating "distinct containers own distinct writable
layers" would have caught this at the model level.
