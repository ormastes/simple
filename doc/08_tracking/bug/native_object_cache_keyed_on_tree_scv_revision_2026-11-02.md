# Native object cache is keyed on the whole-tree SCV revision, not per-module content

- **ID:** native_object_cache_keyed_on_tree_scv_revision_2026-11-02
- **Priority:** P1 (perf; every source change forces a full re-codegen of the closure)
- **Status:** open
- **Owner area:** `src/compiler/80.driver` native capsule / object cache identity
  (`driver_types.spl` capsule identity, `driver_aot_native_output.spl` object reuse);
  related intent: generic-RR HIR-variant object keys (#5745)
- **Found by:** phase-3 runs 19b-23b on the frozen stage2 `C:/dev/p3new/stage2.exe` (ef0681fc0e1)

## Evidence (file-only map, `C:/dev/p3new/objmap/`, 2026-11-02)

| metric | value |
|---|---|
| stage3 closure modules | 1521 |
| `aot-*.o` objects in `C:/dev/p3new` | 1350 |
| distinct modules covered | 623 |
| closure modules with no object | 898 |
| objects on the current revision (`scv-revision-v1-89766ed5…`, tip df3a14d194b) | 144 |
| objects on `23016a5f…` (tips 3273833de3d / 10f3a074bd3) | 1039 |
| objects on `71d98698…` | 167 |

Each `.o.capsule-receipt` records `scv-revision-v1-<hash>`, the snapshot id of the
WHOLE source tree. A one-file workaround on an unrelated module (for example #5796, which
touched only `unicode_17_0_0.spl`) changes the revision, and every previously built
object stops being reused. Phase-3 codegen therefore restarted from about zero after each
landed workaround: 1350 objects were built, but only 623 modules are covered.

## Expected

The object key should be per-module: the module's own MIR/content digest plus the
interface digests of its dependencies, plus target, options and compiler identity.
An unrelated file change must not invalidate the object.

## Workaround (process)

Pin the phase-3 tip (df3a14d194b) until stage3 links. Land further workarounds only when
they are unavoidable, and accept one full re-codegen for each.

## Removal condition

Fixed when a stage3 build reuses all objects after a one-file change outside their closure.
