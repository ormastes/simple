# App Discovery Specification

> 1. app registry clear

<!-- sdn-diagram:id=app_discovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_discovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_discovery_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_discovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Discovery Specification

## Scenarios

### dynamic app discovery — arbitrary path resolution

#### resolves any /sys/apps/ path without registry entry

1. app registry clear
2. app registry load
   - Expected: canonical != nil is true
   - Expected: _unwrap_text(canonical) equals `/sys/apps/my_custom_tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/sys/apps/my_custom_tool")
val canonical = app_registry_canonical_from_bytes(bytes)
expect(canonical != nil).to_equal(true)
expect(_unwrap_text(canonical)).to_equal("/sys/apps/my_custom_tool")
```

</details>

#### rejects non-app paths even with valid bytes

1. app registry clear
2. app registry load
   - Expected: app_registry_canonical_from_bytes(bytes) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/etc/passwd")
expect(app_registry_canonical_from_bytes(bytes)).to_equal(nil)
```

</details>

#### dynamically registers unknown app on cache

1. app registry clear
2. app registry load
3. app registry cache bytes
   - Expected: app_registry_entries().len() equals `initial_count + 1`
   - Expected: entry != nil is true
   - Expected: app_registry_cached_bytes("/sys/apps/new_dynamic_app").len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val initial_count = app_registry_entries().len()
val elf_bytes: [u8] = [0x7F, 0x45, 0x4C, 0x46, 0x02]
app_registry_cache_bytes("/sys/apps/new_dynamic_app", elf_bytes)
expect(app_registry_entries().len()).to_equal(initial_count + 1)
val entry = app_registry_lookup("/sys/apps/new_dynamic_app")
expect(entry != nil).to_equal(true)
expect(app_registry_cached_bytes("/sys/apps/new_dynamic_app").len()).to_equal(5)
```

</details>

### dynamic app discovery — clang and rust loading

#### resolves clang through registry alias

1. app registry clear
2. app registry load
   - Expected: fat32 != nil is true
   - Expected: _unwrap_text(fat32) equals `/SYS/APPS/CLANGSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val fat32 = app_registry_fat32_alias("/sys/apps/clang")
expect(fat32 != nil).to_equal(true)
expect(_unwrap_text(fat32)).to_equal("/SYS/APPS/CLANGSMF.SMF")
```

</details>

#### resolves rust through registry alias

1. app registry clear
2. app registry load
   - Expected: fat32 != nil is true
   - Expected: _unwrap_text(fat32) equals `/SYS/APPS/RUSTSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val fat32 = app_registry_fat32_alias("/sys/apps/rust")
expect(fat32 != nil).to_equal(true)
expect(_unwrap_text(fat32)).to_equal("/SYS/APPS/RUSTSMF.SMF")
```

</details>

#### marks clang and rust as boot seeds

1. app registry clear
2. app registry load
   - Expected: seeds.len() equals `2`
   - Expected: has_clang is true
   - Expected: has_rust is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val seeds = app_registry_boot_seed_entries()
expect(seeds.len()).to_equal(2)
var has_clang = false
var has_rust = false
for seed in seeds:
    if seed.canonical_path == "/sys/apps/clang":
        has_clang = true
    if seed.canonical_path == "/sys/apps/rust":
        has_rust = true
expect(has_clang).to_equal(true)
expect(has_rust).to_equal(true)
```

</details>

#### caches clang executable bytes for loading

1. app registry clear
2. app registry load
3. app registry cache bytes
   - Expected: cached.len() equals `6`
   - Expected: cached[0] equals `0x7F`
   - Expected: cached[3] equals `0x46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val elf_header: [u8] = [0x7F, 0x45, 0x4C, 0x46, 0x02, 0x01]
app_registry_cache_bytes("/sys/apps/clang", elf_header)
val cached = app_registry_cached_bytes("/sys/apps/clang")
expect(cached.len()).to_equal(6)
expect(cached[0]).to_equal(0x7F)
expect(cached[3]).to_equal(0x46)
```

</details>

### dynamic app discovery — FAT32 alias fallback

#### resolves registered path via FAT32 alias

1. app registry clear
2. app registry load
   - Expected: fat32 != nil is true
   - Expected: _unwrap_text(fat32) equals `/SYS/APPS/HELLOSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val fat32 = app_registry_fat32_alias("/sys/apps/hello_world")
expect(fat32 != nil).to_equal(true)
expect(_unwrap_text(fat32)).to_equal("/SYS/APPS/HELLOSMF.SMF")
```

</details>

#### resolves .smf suffix variant via FAT32 alias

1. app registry clear
2. app registry load
   - Expected: fat32 != nil is true
   - Expected: _unwrap_text(fat32) equals `/SYS/APPS/CLANGSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val fat32 = app_registry_fat32_alias("/sys/apps/clang.smf")
expect(fat32 != nil).to_equal(true)
expect(_unwrap_text(fat32)).to_equal("/SYS/APPS/CLANGSMF.SMF")
```

</details>

#### returns nil for unregistered path alias

1. app registry clear
2. app registry load
   - Expected: app_registry_fat32_alias("/sys/apps/unknown_tool") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_fat32_alias("/sys/apps/unknown_tool")).to_equal(nil)
```

</details>

### dynamic app discovery — path canonicalization

#### canonicalizes registered path from bytes

1. app registry clear
2. app registry load
   - Expected: canonical != nil is true
   - Expected: _unwrap_text(canonical) equals `/sys/apps/clang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/sys/apps/clang")
val canonical = app_registry_canonical_from_bytes(bytes)
expect(canonical != nil).to_equal(true)
expect(_unwrap_text(canonical)).to_equal("/sys/apps/clang")
```

</details>

#### canonicalizes .smf suffix from bytes

1. app registry clear
2. app registry load
   - Expected: canonical != nil is true
   - Expected: _unwrap_text(canonical) equals `/sys/apps/rust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/sys/apps/rust.smf")
val canonical = app_registry_canonical_from_bytes(bytes)
expect(canonical != nil).to_equal(true)
expect(_unwrap_text(canonical)).to_equal("/sys/apps/rust")
```

</details>

#### canonicalizes unregistered /sys/apps/ path from bytes

1. app registry clear
2. app registry load
   - Expected: canonical != nil is true
   - Expected: _unwrap_text(canonical) equals `/sys/apps/future_tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/sys/apps/future_tool")
val canonical = app_registry_canonical_from_bytes(bytes)
expect(canonical != nil).to_equal(true)
expect(_unwrap_text(canonical)).to_equal("/sys/apps/future_tool")
```

</details>

### dynamic app discovery — hardcoded fallback completeness

#### hardcoded fallback includes all 18 standard entries

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: app_registry_entries().len() equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
expect(app_registry_entries().len()).to_equal(18)
```

</details>

#### hardcoded fallback covers clang and rust with boot seed

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: clang != nil is true
   - Expected: clang.unwrap().boot_seed is true
   - Expected: rust != nil is true
   - Expected: rust.unwrap().boot_seed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
val clang = app_registry_lookup("/sys/apps/clang")
expect(clang != nil).to_equal(true)
expect(clang.unwrap().boot_seed).to_equal(true)
val rust = app_registry_lookup("/sys/apps/rust")
expect(rust != nil).to_equal(true)
expect(rust.unwrap().boot_seed).to_equal(true)
```

</details>

#### hardcoded fallback reverse-lookups by FAT32 leaf

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: entry != nil is true
   - Expected: entry.unwrap().canonical_path equals `/sys/apps/clang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
val entry = app_registry_lookup_by_fat32("CLANGSMF.SMF")
expect(entry != nil).to_equal(true)
expect(entry.unwrap().canonical_path).to_equal("/sys/apps/clang")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/app_discovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dynamic app discovery — arbitrary path resolution
- dynamic app discovery — clang and rust loading
- dynamic app discovery — FAT32 alias fallback
- dynamic app discovery — path canonicalization
- dynamic app discovery — hardcoded fallback completeness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
