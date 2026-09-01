# Aspect Pack Specification

> Tests covering aspect-pack SMF container and Aspect Catalog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Pack Specification

## Scenarios

### aspect-pack SMF container and Aspect Catalog

#### REQ-APK-01 builds a multi-module pack whose header carries SMF_FLAG_ASPECT_PACK

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-APK-01 builds a multi-module pack whose header carries SMF_FLAG_ASPECT_PACK
   - Expected: built.ok is true
   - Expected: built.module_count equals `3`
   - Expected: handle.ok is true
   - Expected: (handle.flags & APK_FLAG_ASPECT_PACK) != 0 is true
   - Expected: handle.module_count equals `3`
   - Expected: handle.total_size equals `built.bytes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-01 builds a multi-module pack whose header carries SMF_FLAG_ASPECT_PACK")
val built = apk_build_pack_v1(_modules())
expect(built.ok).to_equal(true)
expect(built.module_count).to_equal(3)
val handle = apk_open_pack_v1(built.bytes)
expect(handle.ok).to_equal(true)
expect((handle.flags & APK_FLAG_ASPECT_PACK) != 0).to_equal(true)
expect(handle.module_count).to_equal(3)
expect(handle.total_size).to_equal(built.bytes.len())
```

</details>

#### REQ-APK-02 loads one module byte-exactly from the pack

- REQ-APK-02 loads one module byte-exactly from the pack
   - Expected: load.ok is true
   - Expected: load.found is true
   - Expected: load.aspect_id equals `metrics`
   - Expected: load.payload.len() equals `want.len()`
   - Expected: bytes_to_text(load.payload) equals `bytes_to_text(want)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-02 loads one module byte-exactly from the pack")
val built = apk_build_pack_v1(_modules())
val handle = apk_open_pack_v1(built.bytes)
val load = apk_load_module_v1(built.bytes, handle, "metrics.counters")
expect(load.ok).to_equal(true)
expect(load.found).to_equal(true)
expect(load.aspect_id).to_equal("metrics")
val want = _payload("metrics.counters", 60)
expect(load.payload.len()).to_equal(want.len())
expect(bytes_to_text(load.payload)).to_equal(bytes_to_text(want))
```

</details>

#### REQ-APK-03 the catalog routes a facet key directly to (pack, module)

- REQ-APK-03 the catalog routes a facet key directly to (pack, module)
   - Expected: cat.ok is true
   - Expected: ch.ok is true
   - Expected: ch.entry_count equals `2`
   - Expected: route.ok is true
   - Expected: route.found is true
   - Expected: route.pack_path equals `aspect/obs.apk`
   - Expected: route.module_id equals `trace.spans`
   - Expected: miss.ok is true
   - Expected: miss.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-03 the catalog routes a facet key directly to (pack, module)")
var entries: [ApkCatalogEntryV1] = []
entries.push(ApkCatalogEntryV1(facet_key: "metrics/Debuggable", pack_path: "aspect/obs.apk", module_id: "metrics.counters"))
entries.push(ApkCatalogEntryV1(facet_key: "trace/Traceable", pack_path: "aspect/obs.apk", module_id: "trace.spans"))
val cat = apk_build_catalog_v1(entries)
expect(cat.ok).to_equal(true)
val ch = apk_open_catalog_v1(cat.bytes)
expect(ch.ok).to_equal(true)
expect(ch.entry_count).to_equal(2)
val route = apk_catalog_route_v1(cat.bytes, ch, "trace/Traceable")
expect(route.ok).to_equal(true)
expect(route.found).to_equal(true)
expect(route.pack_path).to_equal("aspect/obs.apk")
expect(route.module_id).to_equal("trace.spans")
# unknown key: clean typed miss, never an error, never a scan fallback
val miss = apk_catalog_route_v1(cat.bytes, ch, "nosuch/Facet")
expect(miss.ok).to_equal(true)
expect(miss.found).to_equal(false)
```

</details>

#### REQ-APK-04 end-to-end: facet -> catalog -> pack -> correct module payload

- REQ-APK-04 end-to-end: facet -> catalog -> pack -> correct module payload
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: got.pack_path equals `aspect/obs.apk`
   - Expected: got.module_id equals `debug.core`
   - Expected: got.aspect_id equals `debug`
   - Expected: bytes_to_text(got.payload) equals `bytes_to_text(_payload("debug.core", 40))`
   - Expected: apk_loader_packs_opened(ld) equals `1`
   - Expected: apk_loader_modules_decompressed(ld) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-04 end-to-end: facet -> catalog -> pack -> correct module payload")
val built = apk_build_pack_v1(_modules())
var entries: [ApkCatalogEntryV1] = []
entries.push(ApkCatalogEntryV1(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk", module_id: "debug.core"))
val cat = apk_build_catalog_v1(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
expect(got.pack_path).to_equal("aspect/obs.apk")
expect(got.module_id).to_equal("debug.core")
expect(got.aspect_id).to_equal("debug")
expect(bytes_to_text(got.payload)).to_equal(bytes_to_text(_payload("debug.core", 40)))
expect(apk_loader_packs_opened(ld)).to_equal(1)
expect(apk_loader_modules_decompressed(ld)).to_equal(1)
```

</details>

#### REQ-APK-05 a join-point route and a facet route never satisfy each other

- REQ-APK-05 a join-point route and a facet route never satisfy each other
   - Expected: cat.ok is true
   - Expected: jp.found is true
   - Expected: jp.module_id equals `trace.spans`
   - Expected: jp.activation equals `APK_ACT_LAZY_PATCHABLE`
   - Expected: apk_catalog_route_v1(cat.bytes, ch, "slot/817").found is false
   - Expected: apk_catalog_route_joinpoint_v1(cat.bytes, ch, "debug/Debuggable").found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-05 a join-point route and a facet route never satisfy each other")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "slot/817", pack_path: "aspect/obs.apk",
    module_id: "trace.spans", entry_kind: APK_ENTRY_JOINPOINT, activation: APK_ACT_LAZY_PATCHABLE, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
expect(cat.ok).to_equal(true)
val ch = apk_open_catalog_v1(cat.bytes)
val jp = apk_catalog_route_joinpoint_v1(cat.bytes, ch, "slot/817")
expect(jp.found).to_equal(true)
expect(jp.module_id).to_equal("trace.spans")
expect(jp.activation).to_equal(APK_ACT_LAZY_PATCHABLE)
# the same key is NOT a facet route, and the facet key is not a slot
expect(apk_catalog_route_v1(cat.bytes, ch, "slot/817").found).to_equal(false)
expect(apk_catalog_route_joinpoint_v1(cat.bytes, ch, "debug/Debuggable").found).to_equal(false)
```

</details>

#### REQ-APK-06 startup routes are listed from the catalog and bound before publication

- REQ-APK-06 startup routes are listed from the catalog and bound before publication
   - Expected: keys.len() equals `1`
   - Expected: keys[0] equals `trace/Traceable`
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", apk_build_pack_v1(_modules()).bytes) is true
   - Expected: apk_activate_startup(ld, cat.bytes) equals `1`
   - Expected: apk_loader_modules_decompressed(ld) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-06 startup routes are listed from the catalog and bound before publication")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "trace/Traceable", pack_path: "aspect/obs.apk",
    module_id: "trace.spans", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_STARTUP, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ch = apk_open_catalog_v1(cat.bytes)
val keys = apk_catalog_startup_keys_v1(cat.bytes, ch)
expect(keys.len()).to_equal(1)
expect(keys[0]).to_equal("trace/Traceable")
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", apk_build_pack_v1(_modules()).bytes)).to_equal(true)
expect(apk_activate_startup(ld, cat.bytes)).to_equal(1)
# exactly the startup module was loaded, not the lazy one
expect(apk_loader_modules_decompressed(ld)).to_equal(1)
```

</details>

#### REQ-APK-07 the pack directory carries the module ABI identity uncompressed

- REQ-APK-07 the pack directory carries the module ABI identity uncompressed
   - Expected: built.ok is true
   - Expected: load.found is true
   - Expected: load.module_abi_hash equals `abi-debug-1`
   - Expected: load.required_core_public_abi_hash equals `core-7`
   - Expected: load.variant_fingerprint equals `vfp-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-07 the pack directory carries the module ABI identity uncompressed")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.core", aspect_id: "debug",
    module_abi_hash: "abi-debug-1", required_core_public_abi_hash: "core-7",
    variant_fingerprint: "vfp-a", payload: _payload("debug.core", 40)))
val built = apk_build_pack_v2(mods)
expect(built.ok).to_equal(true)
val handle = apk_open_pack_v1(built.bytes)
val load = apk_load_module_v1(built.bytes, handle, "debug.core")
expect(load.found).to_equal(true)
expect(load.module_abi_hash).to_equal("abi-debug-1")
expect(load.required_core_public_abi_hash).to_equal("core-7")
expect(load.variant_fingerprint).to_equal("vfp-a")
```

</details>

#### REQ-APK-08 §5.7 atomic activation: the loader generation advances exactly once per successful bind

- REQ-APK-08 §5.7 atomic activation: the loader generation advances exactly once per successful bind
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: apk_loader_generation(ld) equals `0`
   - Expected: first.ok is true
   - Expected: first.generation equals `1`
   - Expected: apk_loader_generation(ld) equals `1`
   - Expected: second.ok is true
   - Expected: second.generation equals `2`
   - Expected: apk_loader_generation(ld) equals `2`
   - Expected: again.from_cache is true
   - Expected: again.generation equals `1`
   - Expected: apk_loader_generation(ld) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-08 §5.7 atomic activation: the loader generation advances exactly once per successful bind")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.core", aspect_id: "debug",
    module_abi_hash: "abi-1", required_core_public_abi_hash: "core-1",
    variant_fingerprint: "vfp-1", payload: _payload("debug.core", 40)))
mods.push(ApkModuleSourceV2(module_id: "trace.spans", aspect_id: "trace",
    module_abi_hash: "abi-2", required_core_public_abi_hash: "core-1",
    variant_fingerprint: "vfp-1", payload: _payload("trace.spans", 50)))
val built = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "trace/Traceable", pack_path: "aspect/obs.apk",
    module_id: "trace.spans", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
expect(apk_loader_generation(ld)).to_equal(0)
val first = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(first.ok).to_equal(true)
expect(first.generation).to_equal(1)
expect(apk_loader_generation(ld)).to_equal(1)
val second = apk_load_facet(ld, cat.bytes, "trace/Traceable")
expect(second.ok).to_equal(true)
expect(second.generation).to_equal(2)
expect(apk_loader_generation(ld)).to_equal(2)
# a repeat acquisition is a cache hit: it reports the SAME generation
# it was originally bound under, and does not bump the epoch again
val again = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(again.from_cache).to_equal(true)
expect(again.generation).to_equal(1)
expect(apk_loader_generation(ld)).to_equal(2)
```

</details>

#### REQ-APK-09 §17 core-ABI and variant-fingerprint gates: SKIPPED when unset, ENFORCED when set

- REQ-APK-09 §17 core-ABI and variant-fingerprint gates: SKIPPED when unset, ENFORCED when set
   - Expected: apk_loader_register_pack(ld_skip, "aspect/obs.apk", built.bytes) is true
   - Expected: skipped.ok is true
   - Expected: apk_loader_register_pack(ld_match, "aspect/obs.apk", built.bytes) is true
   - Expected: matched.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-09 §17 core-ABI and variant-fingerprint gates: SKIPPED when unset, ENFORCED when set")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.core", aspect_id: "debug",
    module_abi_hash: "abi-1", required_core_public_abi_hash: "core-7",
    variant_fingerprint: "vfp-a", payload: _payload("debug.core", 40)))
val built = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
# branch 1: nothing expected -> gate is SKIPPED, load succeeds
val ld_skip = apk_loader_new()
expect(apk_loader_register_pack(ld_skip, "aspect/obs.apk", built.bytes)).to_equal(true)
val skipped = apk_load_facet(ld_skip, cat.bytes, "debug/Debuggable")
expect(skipped.ok).to_equal(true)
# branch 2: matching expectation -> gate is ENFORCED and passes
val ld_match = apk_loader_new()
expect(apk_loader_register_pack(ld_match, "aspect/obs.apk", built.bytes)).to_equal(true)
apk_loader_set_expected_core_abi(ld_match, "core-7")
apk_loader_set_expected_variant_fingerprint(ld_match, "vfp-a")
val matched = apk_load_facet(ld_match, cat.bytes, "debug/Debuggable")
expect(matched.ok).to_equal(true)
```

</details>

#### REQ-APK-10 §14.1 FacetBindingRegistry key: (concrete_type_id, facet_interface_id, generation)

- REQ-APK-10 §14.1 FacetBindingRegistry key: (concrete_type_id, facet_interface_id, generation)
   - Expected: parts.ok is true
   - Expected: parts.concrete_type_id equals `debug`
   - Expected: parts.facet_interface_id equals `Debuggable`
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: loaded.ok is true
   - Expected: by_binding.found is true
   - Expected: by_binding.module_id equals `debug.core`
   - Expected: by_binding.generation equals `loaded.generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-10 §14.1 FacetBindingRegistry key: (concrete_type_id, facet_interface_id, generation)")
val parts = apk_facet_key_parts_v1("debug/Debuggable")
expect(parts.ok).to_equal(true)
expect(parts.concrete_type_id).to_equal("debug")
expect(parts.facet_interface_id).to_equal("Debuggable")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.core", aspect_id: "debug",
    module_abi_hash: "abi-1", required_core_public_abi_hash: "core-1",
    variant_fingerprint: "vfp-1", payload: _payload("debug.core", 40)))
val built = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
val loaded = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(loaded.ok).to_equal(true)
val by_binding = apk_try_facet_binding_v1(ld, "debug", "Debuggable")
expect(by_binding.found).to_equal(true)
expect(by_binding.module_id).to_equal("debug.core")
expect(by_binding.generation).to_equal(loaded.generation)
```

</details>

#### REQ-APK-11 §5.4 binding completeness: apk_build_catalog_v2_checked accepts a route to a declared module

- REQ-APK-11 §5.4 binding completeness: apk_build_catalog_v2_checked accepts a route to a declared module
   - Expected: checked.ok is true
   - Expected: checked.module_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-11 §5.4 binding completeness: apk_build_catalog_v2_checked accepts a route to a declared module")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val checked = apk_build_catalog_v2_checked(entries, ["debug.core", "trace.spans"])
expect(checked.ok).to_equal(true)
expect(checked.module_count).to_equal(1)
```

</details>

#### REQ-APK-12 §9.6 a multi-profile catalog resolves a key inside the SELECTED profile only

- REQ-APK-12 §9.6 a multi-profile catalog resolves a key inside the SELECTED profile only
   - Expected: cat.ok is true
   - Expected: ch.ok is true
   - Expected: ch.profile_count equals `2`
   - Expected: apk_catalog_profile_ids_v1(cat.bytes, ch).len() equals `2`
   - Expected: sel.ok is true
   - Expected: sel.found is true
   - Expected: sel.entry_start equals `0`
   - Expected: sel.entry_count equals `1`
   - Expected: sel.profiles_examined equals `1`
   - Expected: in_min.found is true
   - Expected: in_min.module_id equals `debug.core`
   - Expected: in_full.found is true
   - Expected: in_full.module_id equals `metrics.counters`
   - Expected: absent.ok is true
   - Expected: absent.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-12 §9.6 a multi-profile catalog resolves a key inside the SELECTED profile only")
var entries: [ApkCatalogEntryV2] = []
# profile "minimal" owns entries [0,1); profile "full" owns [1,3)
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "metrics.counters", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "trace/Traceable", pack_path: "aspect/obs.apk",
    module_id: "trace.spans", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
var profiles: [ApkProfileRecordV1] = []
profiles.push(ApkProfileRecordV1(profile_id: "minimal", entry_start: 0, entry_count: 1))
profiles.push(ApkProfileRecordV1(profile_id: "full", entry_start: 1, entry_count: 2))
val cat = apk_build_catalog_v3(entries, profiles)
expect(cat.ok).to_equal(true)
val ch = apk_open_catalog_v1(cat.bytes)
expect(ch.ok).to_equal(true)
expect(ch.profile_count).to_equal(2)
expect(apk_catalog_profile_ids_v1(cat.bytes, ch).len()).to_equal(2)
# selection stops at the FIRST matching record: "must not evaluate
# every profile" is measured, not promised.
val sel = apk_catalog_select_profile_v1(cat.bytes, ch, "minimal")
expect(sel.ok).to_equal(true)
expect(sel.found).to_equal(true)
expect(sel.entry_start).to_equal(0)
expect(sel.entry_count).to_equal(1)
expect(sel.profiles_examined).to_equal(1)
# the SAME key resolves to a DIFFERENT module per profile
val in_min = apk_catalog_route_in_profile_v1(cat.bytes, ch, "minimal", "debug/Debuggable")
expect(in_min.found).to_equal(true)
expect(in_min.module_id).to_equal("debug.core")
val in_full = apk_catalog_route_in_profile_v1(cat.bytes, ch, "full", "debug/Debuggable")
expect(in_full.found).to_equal(true)
expect(in_full.module_id).to_equal("metrics.counters")
# a key owned only by "full" is a clean MISS inside "minimal"
val absent = apk_catalog_route_in_profile_v1(cat.bytes, ch, "minimal", "trace/Traceable")
expect(absent.ok).to_equal(true)
expect(absent.found).to_equal(false)
```

</details>

#### REQ-APK-13 §9.6 a loader routes through its selected profile

- REQ-APK-13 §9.6 a loader routes through its selected profile
   - Expected: cat.ok is true
   - Expected: apk_loader_register_pack(ld_small, "aspect/obs.apk", built.bytes) is true
   - Expected: apk_loader_profile(ld_small) equals `small`
   - Expected: got_small.ok is true
   - Expected: got_small.module_id equals `debug.core`
   - Expected: apk_loader_register_pack(ld_big, "aspect/obs.apk", built.bytes) is true
   - Expected: got_big.ok is true
   - Expected: got_big.module_id equals `trace.spans`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-13 §9.6 a loader routes through its selected profile")
var mods: [ApkModuleSourceV1] = []
mods.push(ApkModuleSourceV1(module_id: "debug.core", aspect_id: "debug", payload: _payload("debug.core", 20)))
mods.push(ApkModuleSourceV1(module_id: "trace.spans", aspect_id: "trace", payload: _payload("trace.spans", 25)))
val built = apk_build_pack_v1(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "x/Facet", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "x/Facet", pack_path: "aspect/obs.apk",
    module_id: "trace.spans", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
var profiles: [ApkProfileRecordV1] = []
profiles.push(ApkProfileRecordV1(profile_id: "small", entry_start: 0, entry_count: 1))
profiles.push(ApkProfileRecordV1(profile_id: "big", entry_start: 1, entry_count: 1))
val cat = apk_build_catalog_v3(entries, profiles)
expect(cat.ok).to_equal(true)
val ld_small = apk_loader_new()
expect(apk_loader_register_pack(ld_small, "aspect/obs.apk", built.bytes)).to_equal(true)
apk_loader_select_profile(ld_small, "small")
expect(apk_loader_profile(ld_small)).to_equal("small")
val got_small = apk_load_facet(ld_small, cat.bytes, "x/Facet")
expect(got_small.ok).to_equal(true)
expect(got_small.module_id).to_equal("debug.core")
val ld_big = apk_loader_new()
expect(apk_loader_register_pack(ld_big, "aspect/obs.apk", built.bytes)).to_equal(true)
apk_loader_select_profile(ld_big, "big")
val got_big = apk_load_facet(ld_big, cat.bytes, "x/Facet")
expect(got_big.ok).to_equal(true)
expect(got_big.module_id).to_equal("trace.spans")
```

</details>

#### REQ-APK-14 §12.2 a co-load cluster is ONE frame: three members, one inflate

- REQ-APK-14 §12.2 a co-load cluster is ONE frame: three members, one inflate
   - Expected: built.ok is true
   - Expected: h.ok is true
   - Expected: apk_pack_cluster_of_v1(built.bytes, h, "units.kg") equals `tiny`
   - Expected: apk_pack_cluster_of_v1(built.bytes, h, "trace.spans") equals ``
   - Expected: cl.ok is true
   - Expected: cl.found is true
   - Expected: cl.member_count equals `3`
   - Expected: cl.frames_inflated equals `1`
   - Expected: bytes_to_text(apk_cluster_member_v1(cl, "units.kg")) equals `bytes_to_text(_payload("units.kg", 11))`
   - Expected: bytes_to_text(apk_cluster_member_v1(cl, "units.s")) equals `bytes_to_text(_payload("units.s", 6))`
   - Expected: cl.bytes_decompressed < built.bytes.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-14 §12.2 a co-load cluster is ONE frame: three members, one inflate")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "units.mm", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.mm", 8)))
mods.push(ApkModuleSourceV3(module_id: "units.kg", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.kg", 11)))
mods.push(ApkModuleSourceV3(module_id: "units.s", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.s", 6)))
mods.push(ApkModuleSourceV3(module_id: "trace.spans", aspect_id: "trace",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("trace.spans", 40)))
val built = apk_build_pack_v3(mods)
expect(built.ok).to_equal(true)
val h = apk_open_pack_v1(built.bytes)
expect(h.ok).to_equal(true)
# cluster membership is decidable from the UNCOMPRESSED directory
expect(apk_pack_cluster_of_v1(built.bytes, h, "units.kg")).to_equal("tiny")
expect(apk_pack_cluster_of_v1(built.bytes, h, "trace.spans")).to_equal("")
val cl = apk_load_cluster_v1(built.bytes, h, "tiny")
expect(cl.ok).to_equal(true)
expect(cl.found).to_equal(true)
expect(cl.member_count).to_equal(3)
# THE claim: three modules cost exactly one inflate
expect(cl.frames_inflated).to_equal(1)
expect(bytes_to_text(apk_cluster_member_v1(cl, "units.kg"))).to_equal(bytes_to_text(_payload("units.kg", 11)))
expect(bytes_to_text(apk_cluster_member_v1(cl, "units.s"))).to_equal(bytes_to_text(_payload("units.s", 6)))
# and §12.3 still holds: the cluster frame is smaller than the pack
expect(cl.bytes_decompressed < built.bytes.len()).to_equal(true)
```

</details>

#### REQ-APK-15 §12.2 a clustered module still loads standalone, byte-exactly

- REQ-APK-15 §12.2 a clustered module still loads standalone, byte-exactly
   - Expected: load.ok is true
   - Expected: load.found is true
   - Expected: bytes_to_text(load.payload) equals `bytes_to_text(_payload("units.kg", 11))`
   - Expected: load.modules_decompressed equals `1`
   - Expected: load.bytes_decompressed < built.bytes.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-15 §12.2 a clustered module still loads standalone, byte-exactly")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "units.mm", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.mm", 8)))
mods.push(ApkModuleSourceV3(module_id: "units.kg", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.kg", 11)))
val built = apk_build_pack_v3(mods)
val h = apk_open_pack_v1(built.bytes)
val load = apk_load_module_v1(built.bytes, h, "units.kg")
expect(load.ok).to_equal(true)
expect(load.found).to_equal(true)
expect(bytes_to_text(load.payload)).to_equal(bytes_to_text(_payload("units.kg", 11)))
# still exactly one inflate, of the cluster frame, never the pack
expect(load.modules_decompressed).to_equal(1)
expect(load.bytes_decompressed < built.bytes.len()).to_equal(true)
```

</details>

#### REQ-APK-16 §11.2 ChunkEntry: cluster members share one chunk, an outsider does not

- REQ-APK-16 §11.2 ChunkEntry: cluster members share one chunk, an outsider does not
   - Expected: c1.found is true
   - Expected: c1.chunk_id equals `c2.chunk_id`
   - Expected: c1.file_offset equals `c2.file_offset`
   - Expected: c1.content_crc32 equals `c2.content_crc32`
   - Expected: c3.found is true
   - Expected: c3.chunk_id != c1.chunk_id is true
   - Expected: c3.kind equals `APK_CHUNK_DEBUG`
   - Expected: c1.kind equals `APK_CHUNK_CODE`
   - Expected: c4.ok is true
   - Expected: c4.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-16 §11.2 ChunkEntry: cluster members share one chunk, an outsider does not")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "units.mm", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.mm", 8)))
mods.push(ApkModuleSourceV3(module_id: "units.kg", aspect_id: "units",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("units.kg", 11)))
mods.push(ApkModuleSourceV3(module_id: "dbg.syms", aspect_id: "debug",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_DEBUG,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("dbg.syms", 30)))
val built = apk_build_pack_v3(mods)
val h = apk_open_pack_v1(built.bytes)
val c1 = apk_pack_chunk_of_v1(built.bytes, h, "units.mm")
val c2 = apk_pack_chunk_of_v1(built.bytes, h, "units.kg")
val c3 = apk_pack_chunk_of_v1(built.bytes, h, "dbg.syms")
expect(c1.found).to_equal(true)
expect(c1.chunk_id).to_equal(c2.chunk_id)
expect(c1.file_offset).to_equal(c2.file_offset)
expect(c1.content_crc32).to_equal(c2.content_crc32)
expect(c3.found).to_equal(true)
expect(c3.chunk_id != c1.chunk_id).to_equal(true)
# the design's separately-split COLD chunk is recorded as such
expect(c3.kind).to_equal(APK_CHUNK_DEBUG)
expect(c1.kind).to_equal(APK_CHUNK_CODE)
# an absent module is a clean miss, not an error
val c4 = apk_pack_chunk_of_v1(built.bytes, h, "nope")
expect(c4.ok).to_equal(true)
expect(c4.found).to_equal(false)
```

</details>

#### REQ-APK-17 §12.2 a STORED, page-aligned hot chunk costs ZERO decompression

- REQ-APK-17 §12.2 a STORED, page-aligned hot chunk costs ZERO decompression
   - Expected: built.ok is true
   - Expected: chunk.alignment equals `4096`
   - Expected: (chunk.file_offset % 4096) equals `0`
   - Expected: chunk.compressed_size equals `chunk.uncompressed_size`
   - Expected: hot.ok is true
   - Expected: bytes_to_text(hot.payload) equals `bytes_to_text(_payload("startup.hot", 30))`
   - Expected: hot.modules_decompressed equals `0`
   - Expected: hot.bytes_decompressed equals `0`
   - Expected: cold.modules_decompressed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-17 §12.2 a STORED, page-aligned hot chunk costs ZERO decompression")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "startup.hot", aspect_id: "startup",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_STORED, alignment: 4096, payload: _payload("startup.hot", 30)))
mods.push(ApkModuleSourceV3(module_id: "cold.rest", aspect_id: "cold",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("cold.rest", 30)))
val built = apk_build_pack_v3(mods)
expect(built.ok).to_equal(true)
val h = apk_open_pack_v1(built.bytes)
val chunk = apk_pack_chunk_of_v1(built.bytes, h, "startup.hot")
expect(chunk.alignment).to_equal(4096)
expect((chunk.file_offset % 4096)).to_equal(0)
expect(chunk.compressed_size).to_equal(chunk.uncompressed_size)
val hot = apk_load_module_v1(built.bytes, h, "startup.hot")
expect(hot.ok).to_equal(true)
expect(bytes_to_text(hot.payload)).to_equal(bytes_to_text(_payload("startup.hot", 30)))
# nothing was decompressed at all — that is what "direct mapping" buys
expect(hot.modules_decompressed).to_equal(0)
expect(hot.bytes_decompressed).to_equal(0)
# the neighbouring ordinary chunk is still deflated
val cold = apk_load_module_v1(built.bytes, h, "cold.rest")
expect(cold.modules_decompressed).to_equal(1)
```

</details>

#### REQ-APK-18 §11.2 required_core_layout_hash is carried and gated on opt-in

- REQ-APK-18 §11.2 required_core_layout_hash is carried and gated on opt-in
   - Expected: apk_load_module_v1(built.bytes, h, "debug.core").required_core_layout_hash equals `layout-9`
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: got.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-18 §11.2 required_core_layout_hash is carried and gated on opt-in")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "debug.core", aspect_id: "debug",
    module_abi_hash: "", required_core_public_abi_hash: "",
    required_core_layout_hash: "layout-9", variant_fingerprint: "",
    cluster_id: "", chunk_kind: APK_CHUNK_CODE, chunk_flags: APK_CHUNK_FLAG_NONE,
    alignment: 1, payload: _payload("debug.core", 20)))
val built = apk_build_pack_v3(mods)
val h = apk_open_pack_v1(built.bytes)
expect(apk_load_module_v1(built.bytes, h, "debug.core").required_core_layout_hash).to_equal("layout-9")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk",
    module_id: "debug.core", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
apk_loader_set_expected_core_layout(ld, "layout-9")
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(true)
```

</details>

#### REQ-APK-19 §14.7 unloading an unpinned facet releases it and retires its generation

- REQ-APK-19 §14.7 unloading an unpinned facet releases it and retires its generation
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: first.ok is true
   - Expected: apk_facet_state_v1(ld, "debug/Debuggable") equals `APK_FC_BOUND`
   - Expected: apk_loader_unloads(ld) equals `0`
   - Expected: un.ok is true
   - Expected: un.released is true
   - Expected: un.quiescing is false
   - Expected: apk_loader_unloads(ld) equals `1`
   - Expected: apk_facet_state_v1(ld, "debug/Debuggable") equals `APK_FC_UNLOADED`
   - Expected: apk_try_facet(ld, "debug/Debuggable").found is false
   - Expected: again.ok is true
   - Expected: again.from_cache is false
   - Expected: again.generation > first.generation is true
   - Expected: apk_loader_packs_opened(ld) equals `opened_before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-19 §14.7 unloading an unpinned facet releases it and retires its generation")
var mods: [ApkModuleSourceV1] = []
mods.push(ApkModuleSourceV1(module_id: "debug.core", aspect_id: "debug", payload: _payload("debug.core", 20)))
val built = apk_build_pack_v1(mods)
var entries: [ApkCatalogEntryV1] = []
entries.push(ApkCatalogEntryV1(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk", module_id: "debug.core"))
val cat = apk_build_catalog_v1(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
val first = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(first.ok).to_equal(true)
expect(apk_facet_state_v1(ld, "debug/Debuggable")).to_equal(APK_FC_BOUND)
expect(apk_loader_unloads(ld)).to_equal(0)
val un = apk_unload_facet_v1(ld, "debug/Debuggable")
expect(un.ok).to_equal(true)
expect(un.released).to_equal(true)
expect(un.quiescing).to_equal(false)
expect(apk_loader_unloads(ld)).to_equal(1)
expect(apk_facet_state_v1(ld, "debug/Debuggable")).to_equal(APK_FC_UNLOADED)
# the resident registry no longer answers for it
expect(apk_try_facet(ld, "debug/Debuggable").found).to_equal(false)
# a re-acquisition is a REAL load again, under a NEW activation epoch
val opened_before = apk_loader_packs_opened(ld)
val again = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(again.ok).to_equal(true)
expect(again.from_cache).to_equal(false)
expect(again.generation > first.generation).to_equal(true)
expect(apk_loader_packs_opened(ld)).to_equal(opened_before + 1)
```

</details>

#### REQ-APK-20 §14.7 a PINNED facet is not freed until its last reference goes

- REQ-APK-20 §14.7 a PINNED facet is not freed until its last reference goes
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes) is true
   - Expected: apk_load_facet(ld, cat.bytes, "debug/Debuggable").ok is true
   - Expected: apk_facet_pin_v1(ld, "debug/Debuggable") is true
   - Expected: apk_facet_refcount_v1(ld, "debug/Debuggable") equals `1`
   - Expected: un.ok is true
   - Expected: un.quiescing is true
   - Expected: un.released is false
   - Expected: apk_loader_unloads(ld) equals `0`
   - Expected: apk_facet_state_v1(ld, "debug/Debuggable") equals `APK_FC_QUIESCING`
   - Expected: apk_facet_unpin_v1(ld, "debug/Debuggable") is true
   - Expected: apk_loader_unloads(ld) equals `1`
   - Expected: apk_facet_state_v1(ld, "debug/Debuggable") equals `APK_FC_UNLOADED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-20 §14.7 a PINNED facet is not freed until its last reference goes")
var mods: [ApkModuleSourceV1] = []
mods.push(ApkModuleSourceV1(module_id: "debug.core", aspect_id: "debug", payload: _payload("debug.core", 20)))
val built = apk_build_pack_v1(mods)
var entries: [ApkCatalogEntryV1] = []
entries.push(ApkCatalogEntryV1(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk", module_id: "debug.core"))
val cat = apk_build_catalog_v1(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/obs.apk", built.bytes)).to_equal(true)
expect(apk_load_facet(ld, cat.bytes, "debug/Debuggable").ok).to_equal(true)
expect(apk_facet_pin_v1(ld, "debug/Debuggable")).to_equal(true)
expect(apk_facet_refcount_v1(ld, "debug/Debuggable")).to_equal(1)
val un = apk_unload_facet_v1(ld, "debug/Debuggable")
expect(un.ok).to_equal(true)
expect(un.quiescing).to_equal(true)
# NOT freed while a reference is still held
expect(un.released).to_equal(false)
expect(apk_loader_unloads(ld)).to_equal(0)
expect(apk_facet_state_v1(ld, "debug/Debuggable")).to_equal(APK_FC_QUIESCING)
# the release happens on the final unpin, and only then
expect(apk_facet_unpin_v1(ld, "debug/Debuggable")).to_equal(true)
expect(apk_loader_unloads(ld)).to_equal(1)
expect(apk_facet_state_v1(ld, "debug/Debuggable")).to_equal(APK_FC_UNLOADED)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/aspect_pack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aspect-pack SMF container and Aspect Catalog.
- aspect-pack SMF container and Aspect Catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0eaae41858e834ad954e53692e7754e6c07f2559b3d9fde759a39e4ecba7f894`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0eaae41858e834ad954e53692e7754e6c07f2559b3d9fde759a39e4ecba7f894`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0eaae41858e834ad954e53692e7754e6c07f2559b3d9fde759a39e4ecba7f894`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/aspect_pack_spec.spl
mirror: doc/06_spec/01_unit/lib/aspect_pack_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/aspect_pack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/aspect_pack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/aspect_pack_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 34 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/aspect_pack_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-01 builds a multi-module pack whose header carries SMF_FLAG_ASPECT_PACK' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-02 loads one module byte-exactly from the pack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-03 the catalog routes a facet key directly to (pack, module)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
