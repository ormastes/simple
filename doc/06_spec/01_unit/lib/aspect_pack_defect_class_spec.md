# Aspect Pack Defect Class Specification

> Tests covering aspect-pack defect class: measured claims and fail-closed errors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Pack Defect Class Specification

## Scenarios

### aspect-pack defect class: measured claims and fail-closed errors

#### REQ-APK-DC-01 POSITIVE CONTROL: one facet load decompresses exactly one of 4 modules and opens only its own pack

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-APK-DC-01 POSITIVE CONTROL: one facet load decompresses exactly one of 4 modules and opens only its own pack
   - Expected: pa.ok is true
   - Expected: pb.ok is true
   - Expected: pa.module_count equals `4`
   - Expected: apk_loader_register_pack(ld, "aspect/a.apk", pa.bytes) is true
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", pb.bytes) is true
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: got.module_id equals `metrics.counters`
   - Expected: bytes_to_text(got.payload) equals `bytes_to_text(_payload("metrics.counters", 70))`
   - Expected: apk_loader_packs_opened(ld) equals `1`
   - Expected: apk_loader_modules_decompressed(ld) equals `1`
   - Expected: apk_loader_bytes_decompressed(ld) equals `selected_frame.len()`
   - Expected: apk_loader_bytes_decompressed(ld) < pa.bytes.len() - APK_HEADER_SIZE_V1 is true
   - Expected: got2.ok is true
   - Expected: got2.found is true
   - Expected: got2.pack_path equals `aspect/b.apk`
   - Expected: got2.module_id equals `debug.hooks`
   - Expected: bytes_to_text(got2.payload) equals `bytes_to_text(_payload("debug.hooks", 55))`
   - Expected: apk_loader_packs_opened(ld) equals `2`
   - Expected: apk_loader_modules_decompressed(ld) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-01 POSITIVE CONTROL: one facet load decompresses exactly one of 4 modules and opens only its own pack")
val pa = apk_build_pack_v1(_pack_a_modules())
val pb = apk_build_pack_v1(_pack_b_modules())
expect(pa.ok).to_equal(true)
expect(pb.ok).to_equal(true)
expect(pa.module_count).to_equal(4)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/a.apk", pa.bytes)).to_equal(true)
expect(apk_loader_register_pack(ld, "aspect/b.apk", pb.bytes)).to_equal(true)

val got = apk_load_facet(ld, _catalog(), "metrics/Observable")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
expect(got.module_id).to_equal("metrics.counters")
expect(bytes_to_text(got.payload)).to_equal(bytes_to_text(_payload("metrics.counters", 70)))

# claim 2: only the routed pack was opened, though two are deployed
expect(apk_loader_packs_opened(ld)).to_equal(1)
# claim 1: exactly ONE of the pack's 4 modules was decompressed,
# and the bytes decompressed are exactly the SELECTED frame's
# compressed size — not the pack's whole data area.
expect(apk_loader_modules_decompressed(ld)).to_equal(1)
val selected_frame = deflate_compress(_payload("metrics.counters", 70))
expect(apk_loader_bytes_decompressed(ld)).to_equal(selected_frame.len())
# strictly less than the sum of all frames (the pack minus header/dir)
expect(apk_loader_bytes_decompressed(ld) < pa.bytes.len() - APK_HEADER_SIZE_V1).to_equal(true)

# a second distinct facet still resolves correctly, from the OTHER pack
val got2 = apk_load_facet(ld, _catalog(), "debug/Debuggable")
expect(got2.ok).to_equal(true)
expect(got2.found).to_equal(true)
expect(got2.pack_path).to_equal("aspect/b.apk")
expect(got2.module_id).to_equal("debug.hooks")
expect(bytes_to_text(got2.payload)).to_equal(bytes_to_text(_payload("debug.hooks", 55)))
expect(apk_loader_packs_opened(ld)).to_equal(2)
expect(apk_loader_modules_decompressed(ld)).to_equal(2)
```

</details>

#### REQ-APK-DC-02 a corrupt SELECTED catalog entry is an explicit error, never a fallback

- REQ-APK-DC-02 a corrupt SELECTED catalog entry is an explicit error, never a fallback
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_CATALOG_CORRUPT`
   - Expected: apk_loader_packs_opened(ld) equals `0`
   - Expected: apk_loader_modules_decompressed(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-02 a corrupt SELECTED catalog entry is an explicit error, never a fallback")
val cat = _catalog()
# entry 1 is first in the body; flip a byte inside its pack_path
# (key "metrics/Observable" is 18 bytes; pack_path starts at
# header + 4 + 18 + 4). The key still matches, the crc must not.
var bad: [u8] = []
var i = 0
while i < cat.len():
    bad.push(cat[i])
    i = i + 1
val flip_at = APK_CATALOG_HEADER_SIZE_V1 + 4 + 18 + 4
bad[flip_at] = ((bad[flip_at] as i64) ^ 255) as u8
val ld = apk_loader_new()
val got = apk_load_facet(ld, bad, "metrics/Observable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_CATALOG_CORRUPT")
# nothing was opened or decompressed on the failure path
expect(apk_loader_packs_opened(ld)).to_equal(0)
expect(apk_loader_modules_decompressed(ld)).to_equal(0)
```

</details>

#### REQ-APK-DC-03 a truncated pack is an explicit error

- REQ-APK-DC-03 a truncated pack is an explicit error
   - Expected: handle.ok is false
   - Expected: handle.error_code equals `APK_TRUNCATED_PACK`
   - Expected: apk_loader_register_pack(ld, "aspect/a.apk", cut) is true
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", apk_build_pack_v1(_pack_b_modules()).bytes) is true
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_TRUNCATED_PACK`
   - Expected: apk_loader_modules_decompressed(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-03 a truncated pack is an explicit error")
val pa = apk_build_pack_v1(_pack_a_modules())
var cut: [u8] = []
var i = 0
while i < pa.bytes.len() - 10:
    cut.push(pa.bytes[i])
    i = i + 1
val handle = apk_open_pack_v1(cut)
expect(handle.ok).to_equal(false)
expect(handle.error_code).to_equal("APK_TRUNCATED_PACK")
# and through the routed loader path as well
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/a.apk", cut)).to_equal(true)
expect(apk_loader_register_pack(ld, "aspect/b.apk", apk_build_pack_v1(_pack_b_modules()).bytes)).to_equal(true)
val got = apk_load_facet(ld, _catalog(), "metrics/Observable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_TRUNCATED_PACK")
expect(apk_loader_modules_decompressed(ld)).to_equal(0)
```

</details>

#### REQ-APK-DC-04 a pack without SMF_FLAG_ASPECT_PACK is rejected, not reinterpreted

- REQ-APK-DC-04 a pack without SMF_FLAG_ASPECT_PACK is rejected, not reinterpreted
   - Expected: handle.ok is false
   - Expected: handle.error_code equals `APK_NOT_ASPECT_PACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-04 a pack without SMF_FLAG_ASPECT_PACK is rejected, not reinterpreted")
val pa = apk_build_pack_v1(_pack_a_modules())
var bad: [u8] = []
var i = 0
while i < pa.bytes.len():
    bad.push(pa.bytes[i])
    i = i + 1
bad[10] = 0   # clear the flags byte (bit0 = APK_FLAG_ASPECT_PACK)
val handle = apk_open_pack_v1(bad)
expect(handle.ok).to_equal(false)
expect(handle.error_code).to_equal("APK_NOT_ASPECT_PACK")
```

</details>

#### REQ-APK-DC-05 a corrupt module frame fails its checksum before decompression

- REQ-APK-DC-05 a corrupt module frame fails its checksum before decompression
   - Expected: handle.ok is true
   - Expected: broken.ok is false
   - Expected: broken.error_code equals `APK_MODULE_CORRUPT`
   - Expected: fine.ok is true
   - Expected: fine.found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-05 a corrupt module frame fails its checksum before decompression")
val pa = apk_build_pack_v1(_pack_a_modules())
var bad: [u8] = []
var i = 0
while i < pa.bytes.len():
    bad.push(pa.bytes[i])
    i = i + 1
# flip the LAST byte: it lies inside the last module's frame
val last = bad.len() - 1
bad[last] = ((bad[last] as i64) ^ 255) as u8
val handle = apk_open_pack_v1(bad)
expect(handle.ok).to_equal(true)
# the corrupted frame belongs to profile.cpu (last module)
val broken = apk_load_module_v1(bad, handle, "profile.cpu")
expect(broken.ok).to_equal(false)
expect(broken.error_code).to_equal("APK_MODULE_CORRUPT")
# a DIFFERENT module in the same pack still loads: corruption of an
# unselected frame cannot break unrelated aspects (independence claim)
val fine = apk_load_module_v1(bad, handle, "log.sinks")
expect(fine.ok).to_equal(true)
expect(fine.found).to_equal(true)
```

</details>

#### REQ-APK-DC-06 a routed pack that is not deployed is an explicit error

- REQ-APK-DC-06 a routed pack that is not deployed is an explicit error
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_PACK_MISSING`
   - Expected: apk_loader_packs_opened(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-06 a routed pack that is not deployed is an explicit error")
val ld = apk_loader_new()
val got = apk_load_facet(ld, _catalog(), "metrics/Observable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_PACK_MISSING")
expect(apk_loader_packs_opened(ld)).to_equal(0)
```

</details>

#### REQ-APK-DC-07 activation policy is decided from the catalog alone: off and manual never load implicitly

- REQ-APK-DC-07 activation policy is decided from the catalog alone: off and manual never load implicitly
   - Expected: apk_loader_register_pack(ld, "aspect/a.apk", apk_build_pack_v1(_pack_a_modules()).bytes) is true
   - Expected: excluded.ok is false
   - Expected: excluded.error_code equals `APK_ASPECT_EXCLUDED`
   - Expected: implicit.ok is false
   - Expected: implicit.error_code equals `APK_ASPECT_MANUAL`
   - Expected: apk_loader_packs_opened(ld) equals `0`
   - Expected: apk_loader_modules_decompressed(ld) equals `0`
   - Expected: manual.ok is true
   - Expected: manual.found is true
   - Expected: manual.module_id equals `profile.mem`
   - Expected: apk_loader_modules_decompressed(ld) equals `1`
   - Expected: apk_load_aspect_manual(ld, cat.bytes, "off/Excluded").error_code equals `APK_ASPECT_EXCLUDED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-07 activation policy is decided from the catalog alone: off and manual never load implicitly")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "off/Excluded", pack_path: "aspect/a.apk",
    module_id: "log.sinks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_OFF, abi_hash: ""))
entries.push(ApkCatalogEntryV2(facet_key: "profile/Manual", pack_path: "aspect/a.apk",
    module_id: "profile.mem", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_MANUAL, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/a.apk", apk_build_pack_v1(_pack_a_modules()).bytes)).to_equal(true)

val excluded = apk_load_facet(ld, cat.bytes, "off/Excluded")
expect(excluded.ok).to_equal(false)
expect(excluded.error_code).to_equal("APK_ASPECT_EXCLUDED")
val implicit = apk_load_facet(ld, cat.bytes, "profile/Manual")
expect(implicit.ok).to_equal(false)
expect(implicit.error_code).to_equal("APK_ASPECT_MANUAL")
# a refused aspect costs no pack open and no decompression at all
expect(apk_loader_packs_opened(ld)).to_equal(0)
expect(apk_loader_modules_decompressed(ld)).to_equal(0)

# explicit aspect.load is permitted for manual; off stays refused
val manual = apk_load_aspect_manual(ld, cat.bytes, "profile/Manual")
expect(manual.ok).to_equal(true)
expect(manual.found).to_equal(true)
expect(manual.module_id).to_equal("profile.mem")
expect(apk_loader_modules_decompressed(ld)).to_equal(1)
expect(apk_load_aspect_manual(ld, cat.bytes, "off/Excluded").error_code).to_equal("APK_ASPECT_EXCLUDED")
```

</details>

#### REQ-APK-DC-08 a second acquisition is I/O free, and try_facet never loads

- REQ-APK-DC-08 a second acquisition is I/O free, and try_facet never loads
   - Expected: apk_loader_register_pack(ld, "aspect/a.apk", apk_build_pack_v1(_pack_a_modules()).bytes) is true
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", apk_build_pack_v1(_pack_b_modules()).bytes) is true
   - Expected: cold.found is false
   - Expected: apk_loader_packs_opened(ld) equals `0`
   - Expected: first.found is true
   - Expected: first.from_cache is false
   - Expected: second.found is true
   - Expected: second.from_cache is true
   - Expected: bytes_to_text(second.payload) equals `bytes_to_text(_payload("metrics.counters", 70))`
   - Expected: apk_loader_packs_opened(ld) equals `opened`
   - Expected: apk_loader_bytes_decompressed(ld) equals `inflated`
   - Expected: apk_loader_modules_decompressed(ld) equals `1`
   - Expected: warm.found is true
   - Expected: warm.from_cache is true
   - Expected: apk_loader_packs_opened(ld) equals `opened`
   - Expected: apk_loader_cache_hits(ld) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-08 a second acquisition is I/O free, and try_facet never loads")
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/a.apk", apk_build_pack_v1(_pack_a_modules()).bytes)).to_equal(true)
expect(apk_loader_register_pack(ld, "aspect/b.apk", apk_build_pack_v1(_pack_b_modules()).bytes)).to_equal(true)

# try_facet BEFORE any load: a clean miss that moves no counter
val cold = apk_try_facet(ld, "metrics/Observable")
expect(cold.found).to_equal(false)
expect(apk_loader_packs_opened(ld)).to_equal(0)

val first = apk_load_facet(ld, _catalog(), "metrics/Observable")
expect(first.found).to_equal(true)
expect(first.from_cache).to_equal(false)
val opened = apk_loader_packs_opened(ld)
val inflated = apk_loader_bytes_decompressed(ld)

val second = apk_load_facet(ld, _catalog(), "metrics/Observable")
expect(second.found).to_equal(true)
expect(second.from_cache).to_equal(true)
expect(bytes_to_text(second.payload)).to_equal(bytes_to_text(_payload("metrics.counters", 70)))
# nothing was reopened and nothing was inflated a second time
expect(apk_loader_packs_opened(ld)).to_equal(opened)
expect(apk_loader_bytes_decompressed(ld)).to_equal(inflated)
expect(apk_loader_modules_decompressed(ld)).to_equal(1)

# and try_facet now answers without I/O
val warm = apk_try_facet(ld, "metrics/Observable")
expect(warm.found).to_equal(true)
expect(warm.from_cache).to_equal(true)
expect(apk_loader_packs_opened(ld)).to_equal(opened)
expect(apk_loader_cache_hits(ld)).to_equal(2)
```

</details>

#### REQ-APK-DC-09 a facet contract ABI mismatch is a load failure, not a best-effort bind

- REQ-APK-DC-09 a facet contract ABI mismatch is a load failure, not a best-effort bind
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes) is true
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_ABI_MISMATCH`
   - Expected: apk_try_facet(ld, "debug/Debuggable").found is false
   - Expected: apk_loader_register_pack(ld2, "aspect/b.apk", pack.bytes) is true
   - Expected: fine.ok is true
   - Expected: fine.found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-09 a facet contract ABI mismatch is a load failure, not a best-effort bind")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.hooks", aspect_id: "debug",
    module_abi_hash: "abi-2", required_core_public_abi_hash: "core-1",
    variant_fingerprint: "vfp", payload: _payload("debug.hooks", 55)))
val pack = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET,
    abi_hash: "abi-1"))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes)).to_equal(true)
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_ABI_MISMATCH")
# a failed bind is never published to the already-bound registry
expect(apk_try_facet(ld, "debug/Debuggable").found).to_equal(false)

# the matching ABI binds
var ok_entries: [ApkCatalogEntryV2] = []
ok_entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET,
    abi_hash: "abi-2"))
val ld2 = apk_loader_new()
expect(apk_loader_register_pack(ld2, "aspect/b.apk", pack.bytes)).to_equal(true)
val fine = apk_load_facet(ld2, apk_build_catalog_v2(ok_entries).bytes, "debug/Debuggable")
expect(fine.ok).to_equal(true)
expect(fine.found).to_equal(true)
```

</details>

#### REQ-APK-DC-10 §17 a core-ABI mismatch is a load failure when the expectation was set, and never advances the generation

- REQ-APK-DC-10 §17 a core-ABI mismatch is a load failure when the expectation was set, and never advances the generation
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes) is true
   - Expected: apk_loader_generation(ld) equals `0`
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_CORE_ABI_MISMATCH`
   - Expected: apk_loader_generation(ld) equals `0`
   - Expected: apk_try_facet(ld, "debug/Debuggable").found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-10 §17 a core-ABI mismatch is a load failure when the expectation was set, and never advances the generation")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.hooks", aspect_id: "debug",
    module_abi_hash: "abi-1", required_core_public_abi_hash: "core-actual",
    variant_fingerprint: "vfp", payload: _payload("debug.hooks", 55)))
val pack = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes)).to_equal(true)
apk_loader_set_expected_core_abi(ld, "core-expected")
expect(apk_loader_generation(ld)).to_equal(0)
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_CORE_ABI_MISMATCH")
# a failed bind never advances the activation epoch, and is never published
expect(apk_loader_generation(ld)).to_equal(0)
expect(apk_try_facet(ld, "debug/Debuggable").found).to_equal(false)
```

</details>

#### REQ-APK-DC-11 §17 a variant-fingerprint mismatch is a load failure when the expectation was set

- REQ-APK-DC-11 §17 a variant-fingerprint mismatch is a load failure when the expectation was set
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes) is true
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_VARIANT_MISMATCH`
   - Expected: apk_loader_generation(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-11 §17 a variant-fingerprint mismatch is a load failure when the expectation was set")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "debug.hooks", aspect_id: "debug",
    module_abi_hash: "abi-1", required_core_public_abi_hash: "core-1",
    variant_fingerprint: "vfp-actual", payload: _payload("debug.hooks", 55)))
val pack = apk_build_pack_v2(mods)
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val cat = apk_build_catalog_v2(entries)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/b.apk", pack.bytes)).to_equal(true)
apk_loader_set_expected_variant_fingerprint(ld, "vfp-expected")
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_VARIANT_MISMATCH")
expect(apk_loader_generation(ld)).to_equal(0)
```

</details>

#### REQ-APK-DC-12 §5.4 binding completeness: apk_build_catalog_v2_checked rejects a route to an undeclared module

- REQ-APK-DC-12 §5.4 binding completeness: apk_build_catalog_v2_checked rejects a route to an undeclared module
   - Expected: checked.ok is false
   - Expected: checked.error_code equals `APK_DANGLING_BINDING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-12 §5.4 binding completeness: apk_build_catalog_v2_checked rejects a route to an undeclared module")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
val checked = apk_build_catalog_v2_checked(entries, ["some.other.module"])
expect(checked.ok).to_equal(false)
expect(checked.error_code).to_equal("APK_DANGLING_BINDING")
```

</details>

#### REQ-APK-DC-13 §5.5 binding uniqueness: two routes to the same module with conflicting contract ABI hashes are rejected

- REQ-APK-DC-13 §5.5 binding uniqueness: two routes to the same module with conflicting contract ABI hashes are rejected
   - Expected: cat.ok is false
   - Expected: cat.error_code equals `APK_BINDING_ABI_CONFLICT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-13 §5.5 binding uniqueness: two routes to the same module with conflicting contract ABI hashes are rejected")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "debug/Debuggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: "abi-1"))
entries.push(ApkCatalogEntryV2(facet_key: "debug/Loggable", pack_path: "aspect/b.apk",
    module_id: "debug.hooks", entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: "abi-2"))
val cat = apk_build_catalog_v2(entries)
expect(cat.ok).to_equal(false)
expect(cat.error_code).to_equal("APK_BINDING_ABI_CONFLICT")
```

</details>

#### REQ-APK-DC-14 §21 E-APACK004: a directory entry that DECLARES an oversized uncompressed size is refused before inflation

- REQ-APK-DC-14 §21 E-APACK004: a directory entry that DECLARES an oversized uncompressed size is refused before inflation
   - Expected: built.ok is true
   - Expected: handle.ok is true
   - Expected: loaded.ok is false
   - Expected: loaded.error_code equals `APK_MODULE_TOO_LARGE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-14 §21 E-APACK004: a directory entry that DECLARES an oversized uncompressed size is refused before inflation")
var mods: [ApkModuleSourceV2] = []
mods.push(ApkModuleSourceV2(module_id: "big.mod", aspect_id: "big",
    module_abi_hash: "", required_core_public_abi_hash: "", variant_fingerprint: "",
    payload: _payload("big.mod", 5)))
val built = apk_build_pack_v2(mods)
expect(built.ok).to_equal(true)
# patch the directory's uncomp_size field (u64, little-endian) for this
# single-entry pack to a value past the 256 MiB decompression limit.
# Layout from APK_HEADER_SIZE_V1: u32 id_len + id("big.mod"=7) +
# u32 aspect_len + aspect("big"=3) + five empty length-prefixed texts
# (module_abi, core_abi, core_layout, variant_fp, cluster_id) = 5 * u32
# + u64 payload_off + u64 comp_size, THEN u64 uncomp_size.
val uncomp_off = APK_HEADER_SIZE_V1 + 4 + 7 + 4 + 3 + 4 + 4 + 4 + 4 + 4 + 8 + 8
var bad: [u8] = []
var i = 0
while i < built.bytes.len():
    bad.push(built.bytes[i])
    i = i + 1
val oversized: i64 = 300000000  # > APK_MAX_MODULE_UNCOMPRESSED_SIZE (268435456)
var k = 0
while k < 8:
    bad[uncomp_off + k] = ((oversized >> (k * 8)) & 255) as u8
    k = k + 1
val handle = apk_open_pack_v1(bad)
expect(handle.ok).to_equal(true)
val loaded = apk_load_module_v1(bad, handle, "big.mod")
expect(loaded.ok).to_equal(false)
expect(loaded.error_code).to_equal("APK_MODULE_TOO_LARGE")
```

</details>

#### REQ-APK-DC-15 §21 E-APACK007: an activation cycle is refused, a deep acyclic chain still loads

- REQ-APK-DC-15 §21 E-APACK007: an activation cycle is refused, a deep acyclic chain still loads
   - Expected: apk_activation_stack_enter_v1(ld, "debug/Debuggable") is true
   - Expected: apk_activation_stack_enter_v1(ld, "debug/Debuggable") is false
   - Expected: apk_activation_stack_enter_v1(ld, "a/A") is true
   - Expected: apk_activation_stack_enter_v1(ld, "b/B") is true
   - Expected: apk_activation_stack_enter_v1(ld, "c/C") is true
   - Expected: apk_activation_stack_enter_v1(ld, "a/A") is true
   - Expected: apk_loader_register_pack(ld, "aspect/obs.apk", apk_build_pack_v1(mods).bytes) is true
   - Expected: got.ok is true
   - Expected: got.found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-15 §21 E-APACK007: an activation cycle is refused, a deep acyclic chain still loads")
val ld = apk_loader_new()
# simulate a facet whose own activation is still in progress: entering
# the SAME key again while it is on the stack is a cycle.
expect(apk_activation_stack_enter_v1(ld, "debug/Debuggable")).to_equal(true)
expect(apk_activation_stack_enter_v1(ld, "debug/Debuggable")).to_equal(false)
apk_activation_stack_exit_v1(ld, "debug/Debuggable")

# a deep chain of DISTINCT keys nested on the same stack is legitimate
# and must not be flagged as a cycle
expect(apk_activation_stack_enter_v1(ld, "a/A")).to_equal(true)
expect(apk_activation_stack_enter_v1(ld, "b/B")).to_equal(true)
expect(apk_activation_stack_enter_v1(ld, "c/C")).to_equal(true)
apk_activation_stack_exit_v1(ld, "c/C")
apk_activation_stack_exit_v1(ld, "b/B")
apk_activation_stack_exit_v1(ld, "a/A")
# after unwinding, the same key sequence can be re-entered cleanly
expect(apk_activation_stack_enter_v1(ld, "a/A")).to_equal(true)
apk_activation_stack_exit_v1(ld, "a/A")

# end to end through the real loader: an ordinary (non-cyclic) load
# still succeeds with the cycle guard wired into the acquire path
var mods: [ApkModuleSourceV1] = []
mods.push(ApkModuleSourceV1(module_id: "debug.core", aspect_id: "debug", payload: _payload("debug.core", 10)))
var entries: [ApkCatalogEntryV1] = []
entries.push(ApkCatalogEntryV1(facet_key: "debug/Debuggable", pack_path: "aspect/obs.apk", module_id: "debug.core"))
val cat = apk_build_catalog_v1(entries)
expect(apk_loader_register_pack(ld, "aspect/obs.apk", apk_build_pack_v1(mods).bytes)).to_equal(true)
val got = apk_load_facet(ld, cat.bytes, "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
```

</details>

#### REQ-APK-DC-16 §9.6 a catalog with two identical profile ids is REJECTED

- REQ-APK-DC-16 §9.6 a catalog with two identical profile ids is REJECTED
   - Expected: built.ok is false
   - Expected: built.error_code equals `APK_DUP_PROFILE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-16 §9.6 a catalog with two identical profile ids is REJECTED")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "a/F", pack_path: "p", module_id: "m",
    entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
var profiles: [ApkProfileRecordV1] = []
profiles.push(ApkProfileRecordV1(profile_id: "dup", entry_start: 0, entry_count: 1))
profiles.push(ApkProfileRecordV1(profile_id: "dup", entry_start: 0, entry_count: 1))
val built = apk_build_catalog_v3(entries, profiles)
expect(built.ok).to_equal(false)
expect(built.error_code).to_equal("APK_DUP_PROFILE")
```

</details>

#### REQ-APK-DC-17 §9.6 a profile naming entries outside the catalog is REJECTED

- REQ-APK-DC-17 §9.6 a profile naming entries outside the catalog is REJECTED
   - Expected: built.ok is false
   - Expected: built.error_code equals `APK_PROFILE_RANGE`
   - Expected: apk_build_catalog_v3(entries, empty_id).error_code equals `APK_PROFILE_EMPTY_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-17 §9.6 a profile naming entries outside the catalog is REJECTED")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "a/F", pack_path: "p", module_id: "m",
    entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
var profiles: [ApkProfileRecordV1] = []
profiles.push(ApkProfileRecordV1(profile_id: "over", entry_start: 0, entry_count: 4))
val built = apk_build_catalog_v3(entries, profiles)
expect(built.ok).to_equal(false)
expect(built.error_code).to_equal("APK_PROFILE_RANGE")
var empty_id: [ApkProfileRecordV1] = []
empty_id.push(ApkProfileRecordV1(profile_id: "", entry_start: 0, entry_count: 1))
expect(apk_build_catalog_v3(entries, empty_id).error_code).to_equal("APK_PROFILE_EMPTY_ID")
```

</details>

#### REQ-APK-DC-18 §9.6 selecting a profile the catalog does not carry is an explicit error

- REQ-APK-DC-18 §9.6 selecting a profile the catalog does not carry is an explicit error
   - Expected: sel.ok is true
   - Expected: sel.found is false
   - Expected: route.ok is false
   - Expected: route.error_code equals `APK_PROFILE_UNKNOWN`
   - Expected: apk_loader_register_pack(ld, "aspect/a.apk", built.bytes) is true
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_PROFILE_UNKNOWN`
   - Expected: apk_loader_packs_opened(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-18 §9.6 selecting a profile the catalog does not carry is an explicit error")
var entries: [ApkCatalogEntryV2] = []
entries.push(ApkCatalogEntryV2(facet_key: "a/F", pack_path: "aspect/a.apk", module_id: "log.sinks",
    entry_kind: APK_ENTRY_FACET, activation: APK_ACT_LAZY_FACET, abi_hash: ""))
var profiles: [ApkProfileRecordV1] = []
profiles.push(ApkProfileRecordV1(profile_id: "only", entry_start: 0, entry_count: 1))
val cat = apk_build_catalog_v3(entries, profiles)
val ch = apk_open_catalog_v1(cat.bytes)
val sel = apk_catalog_select_profile_v1(cat.bytes, ch, "ghost")
expect(sel.ok).to_equal(true)
expect(sel.found).to_equal(false)
val route = apk_catalog_route_in_profile_v1(cat.bytes, ch, "ghost", "a/F")
expect(route.ok).to_equal(false)
expect(route.error_code).to_equal("APK_PROFILE_UNKNOWN")
# and a loader pinned to a nonexistent profile refuses to load rather
# than quietly falling back to whole-catalog routing
val built = apk_build_pack_v1(_pack_a_modules())
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/a.apk", built.bytes)).to_equal(true)
apk_loader_select_profile(ld, "ghost")
val got = apk_load_facet(ld, cat.bytes, "a/F")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_PROFILE_UNKNOWN")
expect(apk_loader_packs_opened(ld)).to_equal(0)
```

</details>

#### REQ-APK-DC-19 §12.2 a co-load cluster whose members contradict each other is REJECTED

- REQ-APK-DC-19 §12.2 a co-load cluster whose members contradict each other is REJECTED
   - Expected: built.ok is false
   - Expected: built.error_code equals `APK_CLUSTER_CHUNK_CONFLICT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-19 §12.2 a co-load cluster whose members contradict each other is REJECTED")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "u.a", aspect_id: "u",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("u.a", 5)))
mods.push(ApkModuleSourceV3(module_id: "u.b", aspect_id: "u",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_DEBUG,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("u.b", 5)))
val built = apk_build_pack_v3(mods)
expect(built.ok).to_equal(false)
expect(built.error_code).to_equal("APK_CLUSTER_CHUNK_CONFLICT")
```

</details>

#### REQ-APK-DC-20 §12.2 corrupting a cluster frame fails ITS members only, never the pack

- REQ-APK-DC-20 §12.2 corrupting a cluster frame fails ITS members only, never the pack
   - Expected: chunk.found is true
   - Expected: h.ok is true
   - Expected: apk_load_module_v1(bad, h, "u.a").error_code equals `APK_MODULE_CORRUPT`
   - Expected: apk_load_module_v1(bad, h, "u.b").error_code equals `APK_MODULE_CORRUPT`
   - Expected: apk_load_cluster_v1(bad, h, "tiny").error_code equals `APK_MODULE_CORRUPT`
   - Expected: solo.ok is true
   - Expected: bytes_to_text(solo.payload) equals `bytes_to_text(_payload("solo", 20))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-20 §12.2 corrupting a cluster frame fails ITS members only, never the pack")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "u.a", aspect_id: "u",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("u.a", 12)))
mods.push(ApkModuleSourceV3(module_id: "u.b", aspect_id: "u",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "tiny", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("u.b", 14)))
mods.push(ApkModuleSourceV3(module_id: "solo", aspect_id: "s",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("solo", 20)))
val built = apk_build_pack_v3(mods)
val h0 = apk_open_pack_v1(built.bytes)
val chunk = apk_pack_chunk_of_v1(built.bytes, h0, "u.a")
expect(chunk.found).to_equal(true)
var bad: [u8] = []
var i = 0
while i < built.bytes.len():
    if i == chunk.file_offset:
        bad.push(((built.bytes[i] as i64) ^ 255) as u8)
    else:
        bad.push(built.bytes[i])
    i = i + 1
val h = apk_open_pack_v1(bad)
expect(h.ok).to_equal(true)
expect(apk_load_module_v1(bad, h, "u.a").error_code).to_equal("APK_MODULE_CORRUPT")
expect(apk_load_module_v1(bad, h, "u.b").error_code).to_equal("APK_MODULE_CORRUPT")
expect(apk_load_cluster_v1(bad, h, "tiny").error_code).to_equal("APK_MODULE_CORRUPT")
# the unclustered neighbour is untouched — §12.3 independence holds
val solo = apk_load_module_v1(bad, h, "solo")
expect(solo.ok).to_equal(true)
expect(bytes_to_text(solo.payload)).to_equal(bytes_to_text(_payload("solo", 20)))
```

</details>

#### REQ-APK-DC-21 §12.2 an empty or unknown cluster id never yields a frame

- REQ-APK-DC-21 §12.2 an empty or unknown cluster id never yields a frame
   - Expected: empty_id.ok is false
   - Expected: empty_id.error_code equals `APK_CLUSTER_EMPTY_ID`
   - Expected: unknown.ok is true
   - Expected: unknown.found is false
   - Expected: unknown.frames_inflated equals `0`
   - Expected: apk_pack_cluster_of_v1(built.bytes, h, "solo") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-21 §12.2 an empty or unknown cluster id never yields a frame")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "solo", aspect_id: "s",
    module_abi_hash: "", required_core_public_abi_hash: "", required_core_layout_hash: "",
    variant_fingerprint: "", cluster_id: "", chunk_kind: APK_CHUNK_CODE,
    chunk_flags: APK_CHUNK_FLAG_NONE, alignment: 1, payload: _payload("solo", 20)))
val built = apk_build_pack_v3(mods)
val h = apk_open_pack_v1(built.bytes)
# an unclustered module must NOT be reachable as if it were a cluster
val empty_id = apk_load_cluster_v1(built.bytes, h, "")
expect(empty_id.ok).to_equal(false)
expect(empty_id.error_code).to_equal("APK_CLUSTER_EMPTY_ID")
val unknown = apk_load_cluster_v1(built.bytes, h, "nope")
expect(unknown.ok).to_equal(true)
expect(unknown.found).to_equal(false)
expect(unknown.frames_inflated).to_equal(0)
expect(apk_pack_cluster_of_v1(built.bytes, h, "solo")).to_equal("")
```

</details>

#### REQ-APK-DC-22 §14.7 unloading a facet that was never bound is an explicit error

- REQ-APK-DC-22 §14.7 unloading a facet that was never bound is an explicit error
   - Expected: un.ok is false
   - Expected: un.error_code equals `APK_UNLOAD_NOT_BOUND`
   - Expected: un.released is false
   - Expected: apk_loader_unloads(ld) equals `0`
   - Expected: apk_facet_state_v1(ld, "never/Bound") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-22 §14.7 unloading a facet that was never bound is an explicit error")
val ld = apk_loader_new()
val un = apk_unload_facet_v1(ld, "never/Bound")
expect(un.ok).to_equal(false)
expect(un.error_code).to_equal("APK_UNLOAD_NOT_BOUND")
expect(un.released).to_equal(false)
expect(apk_loader_unloads(ld)).to_equal(0)
expect(apk_facet_state_v1(ld, "never/Bound")).to_equal(-1)
```

</details>

#### REQ-APK-DC-23 §14.7 a quiescing facet refuses re-acquisition and is not freed

- REQ-APK-DC-23 §14.7 a quiescing facet refuses re-acquisition and is not freed
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", built.bytes) is true
   - Expected: apk_load_facet(ld, _catalog(), "debug/Debuggable").ok is true
   - Expected: apk_facet_pin_v1(ld, "debug/Debuggable") is true
   - Expected: apk_unload_facet_v1(ld, "debug/Debuggable").quiescing is true
   - Expected: again.ok is false
   - Expected: again.error_code equals `APK_ASPECT_QUIESCING`
   - Expected: apk_loader_unloads(ld) equals `0`
   - Expected: apk_facet_state_v1(ld, "debug/Debuggable") equals `APK_FC_QUIESCING`
   - Expected: apk_facet_refcount_v1(ld, "debug/Debuggable") equals `1`
   - Expected: apk_facet_pin_v1(ld, "debug/Debuggable") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-23 §14.7 a quiescing facet refuses re-acquisition and is not freed")
val built = apk_build_pack_v1(_pack_b_modules())
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/b.apk", built.bytes)).to_equal(true)
expect(apk_load_facet(ld, _catalog(), "debug/Debuggable").ok).to_equal(true)
expect(apk_facet_pin_v1(ld, "debug/Debuggable")).to_equal(true)
expect(apk_unload_facet_v1(ld, "debug/Debuggable").quiescing).to_equal(true)
# step 2 of §14.7: NEW acquisitions are refused while quiescing
val again = apk_load_facet(ld, _catalog(), "debug/Debuggable")
expect(again.ok).to_equal(false)
expect(again.error_code).to_equal("APK_ASPECT_QUIESCING")
# and the still-referenced binding was NOT freed by any of that
expect(apk_loader_unloads(ld)).to_equal(0)
expect(apk_facet_state_v1(ld, "debug/Debuggable")).to_equal(APK_FC_QUIESCING)
expect(apk_facet_refcount_v1(ld, "debug/Debuggable")).to_equal(1)
# a new pin on a quiescing binding is refused too
expect(apk_facet_pin_v1(ld, "debug/Debuggable")).to_equal(false)
```

</details>

#### REQ-APK-DC-24 §14.7 unbalanced pin/unpin is refused, never silently accepted

- REQ-APK-DC-24 §14.7 unbalanced pin/unpin is refused, never silently accepted
   - Expected: apk_facet_pin_v1(ld, "debug/Debuggable") is false
   - Expected: apk_facet_unpin_v1(ld, "debug/Debuggable") is false
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", built.bytes) is true
   - Expected: apk_load_facet(ld, _catalog(), "debug/Debuggable").ok is true
   - Expected: apk_facet_unpin_v1(ld, "debug/Debuggable") is false
   - Expected: apk_facet_refcount_v1(ld, "debug/Debuggable") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-24 §14.7 unbalanced pin/unpin is refused, never silently accepted")
val built = apk_build_pack_v1(_pack_b_modules())
val ld = apk_loader_new()
expect(apk_facet_pin_v1(ld, "debug/Debuggable")).to_equal(false)
expect(apk_facet_unpin_v1(ld, "debug/Debuggable")).to_equal(false)
expect(apk_loader_register_pack(ld, "aspect/b.apk", built.bytes)).to_equal(true)
expect(apk_load_facet(ld, _catalog(), "debug/Debuggable").ok).to_equal(true)
# unpinning something that was never pinned must not underflow
expect(apk_facet_unpin_v1(ld, "debug/Debuggable")).to_equal(false)
expect(apk_facet_refcount_v1(ld, "debug/Debuggable")).to_equal(0)
```

</details>

#### REQ-APK-DC-25 §11.2 a core LAYOUT hash mismatch fails the load closed

- REQ-APK-DC-25 §11.2 a core LAYOUT hash mismatch fails the load closed
   - Expected: apk_loader_register_pack(ld, "aspect/b.apk", built.bytes) is true
   - Expected: got.ok is false
   - Expected: got.error_code equals `APK_CORE_LAYOUT_MISMATCH`
   - Expected: apk_loader_generation(ld) equals `0`
   - Expected: apk_try_facet(ld, "debug/Debuggable").found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-APK-DC-25 §11.2 a core LAYOUT hash mismatch fails the load closed")
var mods: [ApkModuleSourceV3] = []
mods.push(ApkModuleSourceV3(module_id: "debug.hooks", aspect_id: "debug",
    module_abi_hash: "", required_core_public_abi_hash: "",
    required_core_layout_hash: "layout-1", variant_fingerprint: "",
    cluster_id: "", chunk_kind: APK_CHUNK_CODE, chunk_flags: APK_CHUNK_FLAG_NONE,
    alignment: 1, payload: _payload("debug.hooks", 20)))
val built = apk_build_pack_v3(mods)
val ld = apk_loader_new()
expect(apk_loader_register_pack(ld, "aspect/b.apk", built.bytes)).to_equal(true)
apk_loader_set_expected_core_layout(ld, "layout-2")
val got = apk_load_facet(ld, _catalog(), "debug/Debuggable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("APK_CORE_LAYOUT_MISMATCH")
# a failed bind never publishes and never advances the epoch
expect(apk_loader_generation(ld)).to_equal(0)
expect(apk_try_facet(ld, "debug/Debuggable").found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/aspect_pack_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aspect-pack defect class: measured claims and fail-closed errors.
- aspect-pack defect class: measured claims and fail-closed errors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `665d18aeb973fe549e53dc7feeaa08f09511c304932d78802340a6b151a2b044`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `665d18aeb973fe549e53dc7feeaa08f09511c304932d78802340a6b151a2b044`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `665d18aeb973fe549e53dc7feeaa08f09511c304932d78802340a6b151a2b044`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/aspect_pack_defect_class_spec.spl
mirror: doc/06_spec/01_unit/lib/aspect_pack_defect_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/aspect_pack_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/aspect_pack_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/aspect_pack_defect_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 26 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/aspect_pack_defect_class_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-DC-01 POSITIVE CONTROL: one facet load decompresses exactly one of 4 modules and opens only its own pack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_defect_class_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-DC-02 a corrupt SELECTED catalog entry is an explicit error, never a fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_defect_class_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APK-DC-03 a truncated pack is an explicit error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
