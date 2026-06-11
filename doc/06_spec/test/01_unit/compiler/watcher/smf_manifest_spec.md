# smf_manifest_spec

> SMF Manifest Specification

<!-- sdn-diagram:id=smf_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_manifest_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_manifest_spec

SMF Manifest Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-MAN-001 to #WATCH-MAN-010 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/smf_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SMF Manifest Specification

Tests manifest creation, SDN serialization round-trip,
entry CRUD, and lookup operations.

## Scenarios

### SmfManifest creation

#### creates empty manifest with version 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mock_manifest()
expect(m.version).to_equal(1)
expect(m.entries.len()).to_equal(0)
```

</details>

#### creates entry with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 12345, "cranelift")
expect(e.source_path).to_equal("src/main.spl")
expect(e.smf_path).to_equal("build/smf/src_main.smf")
expect(e.source_hash).to_equal(12345)
expect(e.backend).to_equal("cranelift")
```

</details>

### SmfManifest operations

#### adds entry via update

1. var m = mock manifest
2. m = mock manifest update
   - Expected: m.entries.len() equals `1`
   - Expected: m.entries.has("src/main.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
m = mock_manifest_update(m, e)
expect(m.entries.len()).to_equal(1)
expect(m.entries.has("src/main.spl")).to_equal(true)
```

</details>

#### overwrites entry with same source_path

1. var m = mock manifest
2. m = mock manifest update
3. m = mock manifest update
   - Expected: m.entries.len() equals `1`
   - Expected: m.entries["src/main.spl"].source_hash equals `200`
   - Expected: m.entries["src/main.spl"].backend equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e1 = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
val e2 = mock_entry("src/main.spl", "build/smf/src_main.smf", 200, "llvm")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
expect(m.entries.len()).to_equal(1)
expect(m.entries["src/main.spl"].source_hash).to_equal(200)
expect(m.entries["src/main.spl"].backend).to_equal("llvm")
```

</details>

#### adds multiple entries

1. var m = mock manifest
2. m = mock manifest update
3. m = mock manifest update
   - Expected: m.entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e1 = mock_entry("src/a.spl", "build/smf/a.smf", 10, "cranelift")
val e2 = mock_entry("src/b.spl", "build/smf/b.smf", 20, "cranelift")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
expect(m.entries.len()).to_equal(2)
```

</details>

#### removes entry

1. var m = mock manifest
2. m = mock manifest update
3. m = mock manifest remove
   - Expected: m.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
m = mock_manifest_update(m, e)
m = mock_manifest_remove(m, "src/main.spl")
expect(m.entries.len()).to_equal(0)
```

</details>

#### remove of nonexistent key is no-op

1. var m = mock manifest
2. m = mock manifest remove
   - Expected: m.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
m = mock_manifest_remove(m, "src/nonexistent.spl")
expect(m.entries.len()).to_equal(0)
```

</details>

### SmfManifest find

#### finds existing entry

1. var m = mock manifest
2. m = mock manifest update
   - Expected: found.? is true
   - Expected: found.unwrap().source_hash equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 42, "cranelift")
m = mock_manifest_update(m, e)
val found = mock_manifest_find(m, "src/main.spl")
expect(found.?).to_equal(true)
expect(found.unwrap().source_hash).to_equal(42)
```

</details>

#### returns nil for missing entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mock_manifest()
val found = mock_manifest_find(m, "src/missing.spl")
expect(found.?).to_equal(false)
```

</details>

### SmfManifest SDN serialization

#### serializes empty manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mock_manifest()
val sdn = mock_to_sdn(m)
expect(sdn).to_contain("smf_manifest:")
expect(sdn).to_contain("version: 1")
```

</details>

#### serializes manifest with entries

1. var m = mock manifest
2. m = mock manifest update


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 999, "cranelift")
m = mock_manifest_update(m, e)
val sdn = mock_to_sdn(m)
expect(sdn).to_contain("entries |source_path, smf_path, source_hash, compiled_at, backend|")
expect(sdn).to_contain("src/main.spl")
expect(sdn).to_contain("build/smf/src_main.smf")
expect(sdn).to_contain("999")
expect(sdn).to_contain("cranelift")
```

</details>

#### round-trips empty manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = mock_manifest()
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.version).to_equal(1)
expect(parsed.entries.len()).to_equal(0)
```

</details>

#### round-trips manifest with single entry

1. var m = mock manifest
2. m = mock manifest update
   - Expected: parsed.entries.len() equals `1`
   - Expected: pe.smf_path equals `build/smf/src_app_cli_main.smf`
   - Expected: pe.source_hash equals `12345`
   - Expected: pe.backend equals `cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e = mock_entry("src/app/cli/main.spl", "build/smf/src_app_cli_main.smf", 12345, "cranelift")
m = mock_manifest_update(m, e)
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.entries.len()).to_equal(1)
val pe = parsed.entries["src/app/cli/main.spl"]
expect(pe.smf_path).to_equal("build/smf/src_app_cli_main.smf")
expect(pe.source_hash).to_equal(12345)
expect(pe.backend).to_equal("cranelift")
```

</details>

#### round-trips manifest with multiple entries

1. var m = mock manifest
2. m = mock manifest update
3. m = mock manifest update
   - Expected: parsed.entries.len() equals `2`
   - Expected: parsed.entries["src/a.spl"].source_hash equals `100`
   - Expected: parsed.entries["src/b.spl"].source_hash equals `200`
   - Expected: parsed.entries["src/b.spl"].backend equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = mock_manifest()
val e1 = mock_entry("src/a.spl", "build/smf/a.smf", 100, "cranelift")
val e2 = mock_entry("src/b.spl", "build/smf/b.smf", 200, "llvm")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.entries.len()).to_equal(2)
expect(parsed.entries["src/a.spl"].source_hash).to_equal(100)
expect(parsed.entries["src/b.spl"].source_hash).to_equal(200)
expect(parsed.entries["src/b.spl"].backend).to_equal("llvm")
```

</details>

#### parses entry line correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "\"src/main.spl\", \"build/smf/main.smf\", 42, 1000, \"cranelift\""
val entry = mock_parse_entry_line(line)
expect(entry.?).to_equal(true)
val e = entry.unwrap()
expect(e.source_path).to_equal("src/main.spl")
expect(e.smf_path).to_equal("build/smf/main.smf")
expect(e.source_hash).to_equal(42)
expect(e.compiled_at).to_equal(1000)
expect(e.backend).to_equal("cranelift")
```

</details>

#### returns nil for malformed entry line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = mock_parse_entry_line("bad data")
expect(entry.?).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
