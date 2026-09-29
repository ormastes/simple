# aspect_pack_smf_section_wiring_spec

> Write a real SMF file whose section table carries `.aspect_pack`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# aspect_pack_smf_section_wiring_spec

Write a real SMF file whose section table carries `.aspect_pack`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Write a real SMF file whose section table carries `.aspect_pack`.

## Scenarios

### aspect pack is a registered SMF section reachable from the load path

#### REQ-APKW-01 SmfWriter emits SectionType.AspectPackDirectory as wire byte 16

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-APKW-01 SmfWriter emits SectionType.AspectPackDirectory as wire byte 16
   - Expected: SectionType.AspectPackDirectory.to_wire_u8() as i64 equals `SMF_SECTION_ASPECT_PACK_DIRECTORY`
   - Expected: SectionType.AspectPackDirectory.name() equals `.aspect_pack`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-01 SmfWriter emits SectionType.AspectPackDirectory as wire byte 16")
expect(SectionType.AspectPackDirectory.to_wire_u8() as i64).to_equal(SMF_SECTION_ASPECT_PACK_DIRECTORY)
expect(SectionType.AspectPackDirectory.name()).to_equal(".aspect_pack")
```

</details>

#### REQ-APKW-02 the written SMF sets SMF_FLAG_ASPECT_PACK and carries the section

- REQ-APKW-02 the written SMF sets SMF_FLAG_ASPECT_PACK and carries the section
   - Expected: _write_pack_smf() is true
   - Expected: reader.header.flags.aspect_pack is true
   - Expected: smf_find_section_by_wire_type(reader, SMF_SECTION_ASPECT_PACK_DIRECTORY) >= 0 is true
   - Expected: smf_has_aspect_pack(reader) is true
   - Expected: extracted.len() equals `_pack_bytes().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-02 the written SMF sets SMF_FLAG_ASPECT_PACK and carries the section")
expect(_write_pack_smf()).to_equal(true)
val reader = match SmfReaderMemory.from_data(_read_smf()):
    case Ok(r): r
    case Err(e): panic("reader: {e}")
# header flag (design §12.1: an old loader must reject this file)
expect(reader.header.flags.aspect_pack).to_equal(true)
# section table entry, found by wire type -- not by index convention
expect(smf_find_section_by_wire_type(reader, SMF_SECTION_ASPECT_PACK_DIRECTORY) >= 0).to_equal(true)
expect(smf_has_aspect_pack(reader)).to_equal(true)
# the section payload is the SMFAPK1 container, byte-exact
val extracted = match smf_aspect_pack_bytes(reader):
    case Ok(b): b
    case Err(e): panic("extract: {e}")
expect(extracted.len()).to_equal(_pack_bytes().len())
```

</details>

#### REQ-APKW-03 ModuleLoader.load registers the pack it found in the section table

- REQ-APKW-03 ModuleLoader.load registers the pack it found in the section table
   - Expected: _write_pack_smf() is true
   - Expected: loader.last_load_aspect_pack_modules equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-03 ModuleLoader.load registers the pack it found in the section table")
expect(_write_pack_smf()).to_equal(true)
var loader = ModuleLoader.with_defaults()
match loader.load(_pack_path()):
    case Error(msg): panic("load failed: {msg}")
    case _: pass
# -1 means "no aspect pack registered by this load" -- i.e. unwired.
expect(loader.last_load_aspect_pack_modules).to_equal(2)
```

</details>

#### REQ-APKW-04 a facet routes through the catalog into the pack that load() opened

- REQ-APKW-04 a facet routes through the catalog into the pack that load() opened
   - Expected: _write_pack_smf() is true
   - Expected: got.error_code equals ``
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: got.module_id equals `debug.core`
   - Expected: got.pack_path equals `_pack_path()`
   - Expected: bytes_to_text(got.payload) equals `bytes_to_text(_payload("debug.core"))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-04 a facet routes through the catalog into the pack that load() opened")
expect(_write_pack_smf()).to_equal(true)
var loader = ModuleLoader.with_defaults()
match loader.load(_pack_path()):
    case Error(msg): panic("load failed: {msg}")
    case _: pass
val got = loader.aspect_facet(_catalog_bytes(), "Widget/Debuggable")
# Without the load-path registration this is APK_PACK_MISSING.
expect(got.error_code).to_equal("")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
expect(got.module_id).to_equal("debug.core")
expect(got.pack_path).to_equal(_pack_path())
expect(bytes_to_text(got.payload)).to_equal(bytes_to_text(_payload("debug.core")))
```

</details>

#### REQ-APKW-05 a module with no aspect-pack section registers nothing

- REQ-APKW-05 a module with no aspect-pack section registers nothing
   - Expected: loader.last_load_aspect_pack_modules equals `-1`
   - Expected: miss.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-05 a module with no aspect-pack section registers nothing")
var loader = ModuleLoader.with_defaults()
# A plain .spl source: no SMF, hence no .aspect_pack section.
match loader.load("test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl"):
    case Error(msg): panic("load failed: {msg}")
    case _: pass
expect(loader.last_load_aspect_pack_modules).to_equal(-1)
val miss = loader.resident_aspect_facet("Widget/Debuggable")
expect(miss.found).to_equal(false)
```

</details>

#### REQ-APKW-06 the section bridge registers the pack with an aspect-pack loader

- REQ-APKW-06 the section bridge registers the pack with an aspect-pack loader
   - Expected: _write_pack_smf() is true
   - Expected: smf_register_aspect_pack(ld, _pack_path(), reader) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-06 the section bridge registers the pack with an aspect-pack loader")
expect(_write_pack_smf()).to_equal(true)
val reader = match SmfReaderMemory.from_data(_read_smf()):
    case Ok(r): r
    case Err(e): panic("reader: {e}")
val ld = apk_loader_new()
# -1 = nothing registered, i.e. the section -> provider bridge is gone.
expect(smf_register_aspect_pack(ld, _pack_path(), reader)).to_equal(2)
```

</details>

#### REQ-APKW-07 a facet routes through the catalog into the SMF-registered pack

- REQ-APKW-07 a facet routes through the catalog into the SMF-registered pack
   - Expected: _write_pack_smf() is true
   - Expected: smf_register_aspect_pack(ld, _pack_path(), reader) equals `2`
   - Expected: got.error_code equals ``
   - Expected: got.found is true
   - Expected: got.module_id equals `debug.core`
   - Expected: bytes_to_text(got.payload) equals `bytes_to_text(_payload("debug.core"))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("REQ-APKW-07 a facet routes through the catalog into the SMF-registered pack")
expect(_write_pack_smf()).to_equal(true)
val reader = match SmfReaderMemory.from_data(_read_smf()):
    case Ok(r): r
    case Err(e): panic("reader: {e}")
val ld = apk_loader_new()
expect(smf_register_aspect_pack(ld, _pack_path(), reader)).to_equal(2)
val got = apk_load_facet(ld, _catalog_bytes(), "Widget/Debuggable")
# Without the registration above this is APK_PACK_MISSING.
expect(got.error_code).to_equal("")
expect(got.found).to_equal(true)
expect(got.module_id).to_equal("debug.core")
expect(bytes_to_text(got.payload)).to_equal(bytes_to_text(_payload("debug.core")))
expect(apk_loader_packs_opened(ld)).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1aedb9b68ce59c881e751fafa48053edeaaba972dac803a0d596ae438f3f433b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1aedb9b68ce59c881e751fafa48053edeaaba972dac803a0d596ae438f3f433b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1aedb9b68ce59c881e751fafa48053edeaaba972dac803a0d596ae438f3f433b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APKW-01 SmfWriter emits SectionType.AspectPackDirectory as wire byte 16' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APKW-02 the written SMF sets SMF_FLAG_ASPECT_PACK and carries the section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-APKW-03 ModuleLoader.load registers the pack it found in the section table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
