# smf_manifest_spec

> Purpose: Prove that SmfManifest creation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_manifest_spec

Purpose: Prove that SmfManifest creation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/watcher/smf_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SmfManifest creation.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### SmfManifest creation

#### creates empty manifest with version 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty manifest with version 1
- Verify: creates empty manifest with version 1
   - Expected: m.version equals `1`
   - Expected: m.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty manifest with version 1")
step("Verify: creates empty manifest with version 1")
# @req: REQ-COMPILER-WATCHER-001
val m = mock_manifest()
expect(m.version).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m.entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### creates entry with all fields

- creates entry with all fields
- Verify: creates entry with all fields
   - Expected: e.source_path equals `src/main.spl`
   - Expected: e.smf_path equals `build/smf/src_main.smf`
   - Expected: e.source_hash equals `12345`
   - Expected: e.backend equals `cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates entry with all fields")
step("Verify: creates entry with all fields")
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 12345, "cranelift")
expect(e.source_path).to_equal("src/main.spl")
expect(e.smf_path).to_equal("build/smf/src_main.smf")
expect(e.source_hash).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(e.backend).to_equal("cranelift")
```

</details>

### SmfManifest operations

#### adds entry via update

- adds entry via update
- Verify: adds entry via update
   - Expected: m.entries.len() equals `1`
   - Expected: m.entries.has("src/main.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds entry via update")
step("Verify: adds entry via update")
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
m = mock_manifest_update(m, e)
expect(m.entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m.entries.has("src/main.spl")).to_equal(true)
```

</details>

#### overwrites entry with same source_path

- overwrites entry with same source_path
- Verify: overwrites entry with same source_path
   - Expected: m.entries.len() equals `1`
   - Expected: m.entries["src/main.spl"].source_hash equals `200`
   - Expected: m.entries["src/main.spl"].backend equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites entry with same source_path")
step("Verify: overwrites entry with same source_path")
var m = mock_manifest()
val e1 = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
val e2 = mock_entry("src/main.spl", "build/smf/src_main.smf", 200, "llvm")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
expect(m.entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m.entries["src/main.spl"].source_hash).to_equal(200)
expect(m.entries["src/main.spl"].backend).to_equal("llvm")
```

</details>

#### adds multiple entries

- adds multiple entries
- Verify: adds multiple entries
   - Expected: m.entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds multiple entries")
step("Verify: adds multiple entries")
var m = mock_manifest()
val e1 = mock_entry("src/a.spl", "build/smf/a.smf", 10, "cranelift")
val e2 = mock_entry("src/b.spl", "build/smf/b.smf", 20, "cranelift")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
expect(m.entries.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### removes entry

- removes entry
- Verify: removes entry
   - Expected: m.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes entry")
step("Verify: removes entry")
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 100, "cranelift")
m = mock_manifest_update(m, e)
m = mock_manifest_remove(m, "src/main.spl")
expect(m.entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### remove of nonexistent key is no-op

- remove of nonexistent key is no-op
- Verify: remove of nonexistent key is no-op
   - Expected: m.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove of nonexistent key is no-op")
step("Verify: remove of nonexistent key is no-op")
var m = mock_manifest()
m = mock_manifest_remove(m, "src/nonexistent.spl")
expect(m.entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### SmfManifest find

#### finds existing entry

- finds existing entry
- Verify: finds existing entry
   - Expected: found != nil is true
   - Expected: found.unwrap().source_hash equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds existing entry")
step("Verify: finds existing entry")
var m = mock_manifest()
val e = mock_entry("src/main.spl", "build/smf/src_main.smf", 42, "cranelift")
m = mock_manifest_update(m, e)
val found = mock_manifest_find(m, "src/main.spl")
expect(found != nil).to_equal(true)
expect(found.unwrap().source_hash).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### returns nil for missing entry

- returns nil for missing entry
- Verify: returns nil for missing entry
   - Expected: found != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for missing entry")
step("Verify: returns nil for missing entry")
val m = mock_manifest()
val found = mock_manifest_find(m, "src/missing.spl")
expect(found != nil).to_equal(false)
```

</details>

### SmfManifest SDN serialization

#### serializes empty manifest

- serializes empty manifest
- Verify: serializes empty manifest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty manifest")
step("Verify: serializes empty manifest")
val m = mock_manifest()
val sdn = mock_to_sdn(m)
expect(sdn).to_contain("smf_manifest:")
expect(sdn).to_contain("version: 1")
```

</details>

#### serializes manifest with entries

- serializes manifest with entries
- Verify: serializes manifest with entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes manifest with entries")
step("Verify: serializes manifest with entries")
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

- round-trips empty manifest
- Verify: round-trips empty manifest
   - Expected: parsed.version equals `1`
   - Expected: parsed.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips empty manifest")
step("Verify: round-trips empty manifest")
val m = mock_manifest()
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.version).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(parsed.entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### round-trips manifest with single entry

- round-trips manifest with single entry
- Verify: round-trips manifest with single entry
   - Expected: parsed.entries.len() equals `1`
   - Expected: pe.smf_path equals `build/smf/src_app_cli_main.smf`
   - Expected: pe.source_hash equals `12345`
   - Expected: pe.backend equals `cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips manifest with single entry")
step("Verify: round-trips manifest with single entry")
var m = mock_manifest()
val e = mock_entry("src/app/cli/main.spl", "build/smf/src_app_cli_main.smf", 12345, "cranelift")
m = mock_manifest_update(m, e)
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val pe = parsed.entries["src/app/cli/main.spl"]
expect(pe.smf_path).to_equal("build/smf/src_app_cli_main.smf")
expect(pe.source_hash).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(pe.backend).to_equal("cranelift")
```

</details>

#### round-trips manifest with multiple entries

- round-trips manifest with multiple entries
- Verify: round-trips manifest with multiple entries
   - Expected: parsed.entries.len() equals `2`
   - Expected: parsed.entries["src/a.spl"].source_hash equals `100`
   - Expected: parsed.entries["src/b.spl"].source_hash equals `200`
   - Expected: parsed.entries["src/b.spl"].backend equals `llvm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips manifest with multiple entries")
step("Verify: round-trips manifest with multiple entries")
var m = mock_manifest()
val e1 = mock_entry("src/a.spl", "build/smf/a.smf", 100, "cranelift")
val e2 = mock_entry("src/b.spl", "build/smf/b.smf", 200, "llvm")
m = mock_manifest_update(m, e1)
m = mock_manifest_update(m, e2)
val sdn = mock_to_sdn(m)
val parsed = mock_from_sdn(sdn)
expect(parsed.entries.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(parsed.entries["src/a.spl"].source_hash).to_equal(100)
expect(parsed.entries["src/b.spl"].source_hash).to_equal(200)
expect(parsed.entries["src/b.spl"].backend).to_equal("llvm")
```

</details>

#### parses entry line correctly

- parses entry line correctly
- Verify: parses entry line correctly
   - Expected: entry != nil is true
   - Expected: e.source_path equals `src/main.spl`
   - Expected: e.smf_path equals `build/smf/main.smf`
   - Expected: e.source_hash equals `42`
   - Expected: e.compiled_at equals `1000`
   - Expected: e.backend equals `cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses entry line correctly")
step("Verify: parses entry line correctly")
val line = "\"src/main.spl\", \"build/smf/main.smf\", 42, 1000, \"cranelift\""
val entry = mock_parse_entry_line(line)
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.source_path).to_equal("src/main.spl")
expect(e.smf_path).to_equal("build/smf/main.smf")
expect(e.source_hash).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(e.compiled_at).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
expect(e.backend).to_equal("cranelift")
```

</details>

#### returns nil for malformed entry line

- returns nil for malformed entry line
- Verify: returns nil for malformed entry line
   - Expected: entry != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for malformed entry line")
step("Verify: returns nil for malformed entry line")
val entry = mock_parse_entry_line("bad data")
expect(entry != nil).to_equal(false)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-WATCHER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60bca88f945177bd901b7dd99b5b207f4229a28cd9971937d6379bd3d5a52120`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60bca88f945177bd901b7dd99b5b207f4229a28cd9971937d6379bd3d5a52120`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60bca88f945177bd901b7dd99b5b207f4229a28cd9971937d6379bd3d5a52120`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/watcher/smf_manifest_spec.spl
mirror: doc/06_spec/unit/compiler/watcher/smf_manifest_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/watcher/smf_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/watcher/smf_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/watcher/smf_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/watcher/smf_manifest_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty manifest with version 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/watcher/smf_manifest_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates entry with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/watcher/smf_manifest_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds entry via update' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
