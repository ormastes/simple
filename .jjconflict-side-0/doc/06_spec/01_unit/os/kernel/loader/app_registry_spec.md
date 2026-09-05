# App Registry Specification

> 1. app registry clear

<!-- sdn-diagram:id=app_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_registry_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Registry Specification

## Scenarios

### app registry manifest parser

#### parses a well-formed manifest

1. app registry clear
2. app registry load
   - Expected: app_registry_is_loaded() is true
   - Expected: app_registry_entries().len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_is_loaded()).to_equal(true)
expect(app_registry_entries().len()).to_equal(4)
```

</details>

#### skips comments and blank lines

1. app registry clear
2. app registry load
   - Expected: app_registry_entries().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load("# comment\n\n/sys/apps/a|A.SMF|false\n# another\n")
expect(app_registry_entries().len()).to_equal(1)
```

</details>

#### skips malformed lines

1. app registry clear
2. app registry load
   - Expected: app_registry_entries().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load("bad line\n/sys/apps/a|A.SMF|false\nincomplete|only\n")
expect(app_registry_entries().len()).to_equal(1)
```

</details>

### app registry lookup

#### looks up by canonical path

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.fat32_leaf equals `CLANGSMF.SMF`
   - Expected: e.boot_seed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup("/sys/apps/clang")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.fat32_leaf).to_equal("CLANGSMF.SMF")
expect(e.boot_seed).to_equal(true)
```

</details>

#### resolves .smf suffix variants

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.canonical_path equals `/sys/apps/clang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup("/sys/apps/clang.smf")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.canonical_path).to_equal("/sys/apps/clang")
```

</details>

#### returns nil for unknown paths

1. app registry clear
2. app registry load
   - Expected: app_registry_lookup("/sys/apps/unknown") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_lookup("/sys/apps/unknown")).to_equal(nil)
```

</details>

#### looks up by FAT32 leaf

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.canonical_path equals `/sys/apps/clang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup_by_fat32("CLANGSMF.SMF")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.canonical_path).to_equal("/sys/apps/clang")
```

</details>

#### looks up by full FAT32 path with /SYS/APPS/ prefix

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.canonical_path equals `/sys/apps/clang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup_by_fat32("/SYS/APPS/CLANGSMF.SMF")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.canonical_path).to_equal("/sys/apps/clang")
```

</details>

#### looks up by root-prefixed FAT32 path

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.canonical_path equals `/sys/apps/rust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup_by_fat32("/RUSTSMF.SMF")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.canonical_path).to_equal("/sys/apps/rust")
```

</details>

### app registry aliases

#### returns FAT32 alias path

1. app registry clear
2. app registry load
   - Expected: fat32_path != nil is true
   - Expected: _unwrap_text(fat32_path) equals `/SYS/APPS/CLANGSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val fat32_path = app_registry_fat32_alias("/sys/apps/clang")
expect(fat32_path != nil).to_equal(true)
expect(_unwrap_text(fat32_path)).to_equal("/SYS/APPS/CLANGSMF.SMF")
```

</details>

#### returns root alias path

1. app registry clear
2. app registry load
   - Expected: root_path != nil is true
   - Expected: _unwrap_text(root_path) equals `/RUSTSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val root_path = app_registry_root_alias("/sys/apps/rust")
expect(root_path != nil).to_equal(true)
expect(_unwrap_text(root_path)).to_equal("/RUSTSMF.SMF")
```

</details>

#### returns nil for unknown path alias

1. app registry clear
2. app registry load
   - Expected: app_registry_fat32_alias("/sys/apps/unknown") equals `nil`
   - Expected: app_registry_root_alias("/sys/apps/unknown") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_fat32_alias("/sys/apps/unknown")).to_equal(nil)
expect(app_registry_root_alias("/sys/apps/unknown")).to_equal(nil)
```

</details>

### app registry canonicalization

#### canonicalizes registered path bytes

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

#### canonicalizes unregistered /sys/apps/ path bytes

1. app registry clear
2. app registry load
   - Expected: canonical != nil is true
   - Expected: _unwrap_text(canonical) equals `/sys/apps/new_tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val bytes = rt_text_to_bytes("/sys/apps/new_tool")
val canonical = app_registry_canonical_from_bytes(bytes)
expect(canonical != nil).to_equal(true)
expect(_unwrap_text(canonical)).to_equal("/sys/apps/new_tool")
```

</details>

#### returns nil for non-app paths

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
val bytes = rt_text_to_bytes("/etc/config")
expect(app_registry_canonical_from_bytes(bytes)).to_equal(nil)
```

</details>

### app registry cache

#### round-trips cached bytes

1. app registry clear
2. app registry load
3. app registry cache bytes
   - Expected: cached.len() equals `4`
   - Expected: cached[0] equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val data: [u8] = [0x7F, 0x45, 0x4C, 0x46]
app_registry_cache_bytes("/sys/apps/clang", data)
val cached = app_registry_cached_bytes("/sys/apps/clang")
expect(cached.len()).to_equal(4)
expect(cached[0]).to_equal(0x7F)
```

</details>

#### returns empty for uncached paths

1. app registry clear
2. app registry load
   - Expected: app_registry_cached_bytes("/sys/apps/clang").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_cached_bytes("/sys/apps/clang").len()).to_equal(0)
```

</details>

#### auto-registers unregistered path on cache

1. app registry clear
2. app registry load
3. app registry cache bytes
   - Expected: entry != nil is true
   - Expected: app_registry_cached_bytes("/sys/apps/new_tool").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val data: [u8] = [0x01, 0x02]
app_registry_cache_bytes("/sys/apps/new_tool", data)
val entry = app_registry_lookup("/sys/apps/new_tool")
expect(entry != nil).to_equal(true)
expect(app_registry_cached_bytes("/sys/apps/new_tool").len()).to_equal(2)
```

</details>

### app registry boot seed

#### filters boot seed entries

1. app registry clear
2. app registry load
   - Expected: seeds.len() equals `2`
   - Expected: seeds[0].canonical_path equals `/sys/apps/clang`
   - Expected: seeds[1].canonical_path equals `/sys/apps/rust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val seeds = app_registry_boot_seed_entries()
expect(seeds.len()).to_equal(2)
expect(seeds[0].canonical_path).to_equal("/sys/apps/clang")
expect(seeds[1].canonical_path).to_equal("/sys/apps/rust")
```

</details>

### app registry dynamic registration

#### registers a new entry

1. app registry clear
2. app registry register
   - Expected: app_registry_entries().len() equals `1`
   - Expected: fat32_path != nil is true
   - Expected: _unwrap_text(fat32_path) equals `/SYS/APPS/GAMESMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_register("/sys/apps/game", "GAMESMF.SMF", false)
expect(app_registry_entries().len()).to_equal(1)
val fat32_path = app_registry_fat32_alias("/sys/apps/game")
expect(fat32_path != nil).to_equal(true)
expect(_unwrap_text(fat32_path)).to_equal("/SYS/APPS/GAMESMF.SMF")
```

</details>

#### updates existing entry on re-register

1. app registry clear
2. app registry register
3. app registry register
   - Expected: app_registry_entries().len() equals `1`
   - Expected: e.fat32_leaf equals `GAME2.SMF`
   - Expected: e.boot_seed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_register("/sys/apps/game", "GAMESMF.SMF", false)
app_registry_register("/sys/apps/game", "GAME2.SMF", true)
expect(app_registry_entries().len()).to_equal(1)
val entry = app_registry_lookup("/sys/apps/game")
val e = entry.unwrap()
expect(e.fat32_leaf).to_equal("GAME2.SMF")
expect(e.boot_seed).to_equal(true)
```

</details>

### app registry hardcoded fallback

#### populates all 19 standard entries

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: app_registry_is_loaded() is true
   - Expected: app_registry_entries().len() equals `19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
expect(app_registry_is_loaded()).to_equal(true)
expect(app_registry_entries().len()).to_equal(19)
```

</details>

#### resolves clang and rust from fallback

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: clang != nil is true
   - Expected: ce.fat32_leaf equals `CLANGSMF.SMF`
   - Expected: ce.boot_seed is true
   - Expected: rust != nil is true
   - Expected: re.fat32_leaf equals `RUSTSMF.SMF`
   - Expected: re.boot_seed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
val clang = app_registry_lookup("/sys/apps/clang")
expect(clang != nil).to_equal(true)
val ce = clang.unwrap()
expect(ce.fat32_leaf).to_equal("CLANGSMF.SMF")
expect(ce.boot_seed).to_equal(true)
val rust = app_registry_lookup("/sys/apps/rust")
expect(rust != nil).to_equal(true)
val re = rust.unwrap()
expect(re.fat32_leaf).to_equal("RUSTSMF.SMF")
expect(re.boot_seed).to_equal(true)
```

</details>

#### resolves all 18 FAT32 aliases from fallback

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: app_registry_fat32_alias("/sys/apps/info") != nil is true
   - Expected: app_registry_fat32_alias("/sys/apps/browser_demo") != nil is true
   - Expected: app_registry_fat32_alias("/sys/apps/simple_compiler") != nil is true
   - Expected: app_registry_fat32_alias("/sys/apps/llvm") != nil is true
   - Expected: app_registry_fat32_alias("/sys/apps/wine_hello") != nil is true
   - Expected: app_registry_fat32_alias("/sys/apps/simple") != nil is true
   - Expected: simple_smf != nil is true
   - Expected: _unwrap_text(simple_smf) equals `/SYS/APPS/SIMPLSTC.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
expect(app_registry_fat32_alias("/sys/apps/info") != nil).to_equal(true)
expect(app_registry_fat32_alias("/sys/apps/browser_demo") != nil).to_equal(true)
expect(app_registry_fat32_alias("/sys/apps/simple_compiler") != nil).to_equal(true)
expect(app_registry_fat32_alias("/sys/apps/llvm") != nil).to_equal(true)
expect(app_registry_fat32_alias("/sys/apps/wine_hello") != nil).to_equal(true)
expect(app_registry_fat32_alias("/sys/apps/simple") != nil).to_equal(true)
val simple_smf = app_registry_fat32_alias("/sys/apps/simple.smf")
expect(simple_smf != nil).to_equal(true)
expect(_unwrap_text(simple_smf)).to_equal("/SYS/APPS/SIMPLSTC.SMF")
```

</details>

#### normalizes shell-style executable paths through fallback aliases

1. app registry clear
2. app registry load hardcoded fallback
   - Expected: _unwrap_text(app_registry_fat32_alias("/bin/simple")) equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _unwrap_text(app_registry_fat32_alias("/usr/bin/simple")) equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _unwrap_text(app_registry_fat32_alias("/bin/sh")) equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: _unwrap_text(app_registry_fat32_alias("/usr/bin/shell")) equals `/SYS/APPS/SHELLSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load_hardcoded_fallback()
expect(_unwrap_text(app_registry_fat32_alias("/bin/simple"))).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_unwrap_text(app_registry_fat32_alias("/usr/bin/simple"))).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_unwrap_text(app_registry_fat32_alias("/bin/sh"))).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(_unwrap_text(app_registry_fat32_alias("/usr/bin/shell"))).to_equal("/SYS/APPS/SHELLSMF.SMF")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/app_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app registry manifest parser
- app registry lookup
- app registry aliases
- app registry canonicalization
- app registry cache
- app registry boot seed
- app registry dynamic registration
- app registry hardcoded fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
