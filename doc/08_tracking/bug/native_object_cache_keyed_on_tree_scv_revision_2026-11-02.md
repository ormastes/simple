# Native object cache is keyed on the whole-tree SCV revision, not per-module content

- **ID:** native_object_cache_keyed_on_tree_scv_revision_2026-11-02
- **Priority:** P1 (perf; every source change forces a full re-codegen of the closure)
- **Status:** fixed (PR #5811, 04c260209a: native objects keyed per module, not per SCV tree revision; merged into release/1.0.0, verified 2026-11-02); residual inputs listed below
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

## Fix (lane mp-1, 2026-11-02)

- `src/compiler/80.driver/cache/native_object_source_key_v1.spl`: revision-neutral
  source key (`scv-snapshot:<relative path>` for paths under
  `build/scv/snapshots/scv-revision-v1-<id>/`, unchanged otherwise).
- `FrozenNativeModuleCapsuleV1.expected_identity()` (receipt line 2) now uses that key
  instead of the absolute snapshot path. Content is still bound by source identity,
  MIR identity, storage snapshot, witness, backend/provider, target/cpu/opt/release and
  object path; the cache scope directory still carries compiler/options/environment.
- `build_cache_rebind_scv_snapshot_all_v1` (incremental.spl), in one indexed pass before the native loop, moves each unique BuildCache
  entry recorded under a prior revision onto the current snapshot path before lookup;
  validity (content hash, witness, capsule receipt bytes) is unchanged. Ambiguous
  prior revisions fail closed.
- Spec: `test/01_unit/compiler/driver/native_object_source_key_spec.spl`.

## Residual (not changed here)

- Compiler identity folds the live `src/compiler` and `src/lib` tree fingerprints
  (`native_build_compiler_source_fingerprint`, `native_build_stdlib_source_fingerprint`).
  When the build runs from a checkout, an edit under `src/lib` or `src/compiler`
  still changes the cache scope directory for every object. This needs a separate
  decision: should a compiled (non-interpreted) compiler drop those fingerprints?
- Module witnesses that come back `ambiguous-resolution-fact` never match, so those
  modules can only be reused through the phase-2 manifest route.
- MIR that embeds absolute source paths (spans, panic locations) changes the MIR
  identity per revision. That is real object content, not a key bug.
- Old receipts still carry the absolute path, so the first build after this change
  rebuilds once.
- `dep_iface_gate_*_v2` folds rows over ABSOLUTE dependency paths, so a rebound entry
  WITH recorded dependencies never revalidates across revisions. Native AOT entries
  record `dependencies: []`, so the native path is unaffected; other BuildCache users
  would need a path-neutral fold (one-time format change).
