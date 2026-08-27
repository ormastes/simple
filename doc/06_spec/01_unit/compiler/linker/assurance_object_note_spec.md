# assurance_object_note_spec

> AssuranceObjectNoteV1 specification (WP-20 remainder, aerospace hardening

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# assurance_object_note_spec

AssuranceObjectNoteV1 specification (WP-20 remainder, aerospace hardening

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/assurance_object_note_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

AssuranceObjectNoteV1 specification (WP-20 remainder, aerospace hardening
plan). v1 / PLACEHOLDER schema -- see the doc comment on AssuranceObjectNoteV1
in compiler.backend.linker.smf_writer for the full rationale and field
mapping to WP-19/WP-3/WP-16. This is not a final certification schema.

Covers:
  (a) AssuranceObjectNoteV1.to_bytes() produces real, byte-offset-exact
      serialized bytes -- not just non-empty.
  (b) The note attaches to an SmfWriter via add_assurance_note_section() and
      appears as real payload in SmfWriter.write()'s output (reuses WP-20's
      now-real writer, commit ca63353f7f1).

## Scenarios

### AssuranceObjectNoteV1.to_bytes() real byte serialization

#### produces real, non-empty bytes with the expected total length

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces real, non-empty bytes with the expected total length
   - Expected: bytes.len() equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces real, non-empty bytes with the expected total length")
val note = build_test_note()
val bytes = note.to_bytes()
# 16 + hash_len(64) + profile_len(8) + 32 = 120
expect(bytes.len()).to_equal(120)
```

</details>

#### writes the magic, version, hash length, and hash bytes at exact offsets

- writes the magic, version, hash length, and hash bytes at exact offsets
   - Expected: bytes[0] equals `65u8`
   - Expected: bytes[1] equals `79u8`
   - Expected: bytes[2] equals `78u8`
   - Expected: bytes[3] equals `49u8`
   - Expected: bytes[4] equals `1u8`
   - Expected: bytes[5] equals `0u8`
   - Expected: bytes[8] equals `64u8`
   - Expected: bytes[9] equals `0u8`
   - Expected: bytes[12] equals `97u8`
   - Expected: bytes[13] equals `98u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes the magic, version, hash length, and hash bytes at exact offsets")
val note = build_test_note()
val bytes = note.to_bytes()
# magic "AON1"
expect(bytes[0]).to_equal(65u8)
expect(bytes[1]).to_equal(79u8)
expect(bytes[2]).to_equal(78u8)
expect(bytes[3]).to_equal(49u8)
# version = 1 (u32 LE)
expect(bytes[4]).to_equal(1u8)
expect(bytes[5]).to_equal(0u8)
# hash_len = 64 (u32 LE)
expect(bytes[8]).to_equal(64u8)
expect(bytes[9]).to_equal(0u8)
# hash bytes start at offset 12: 'a'=97, 'b'=98
expect(bytes[12]).to_equal(97u8)
expect(bytes[13]).to_equal(98u8)
```

</details>

#### writes the profile length/bytes and the three obligation counts at exact offsets

- writes the profile length/bytes and the three obligation counts at exact offsets
   - Expected: bytes[76] equals `8u8)   # len("critical") = 8`
   - Expected: bytes[77] equals `0u8`
   - Expected: bytes[80] equals `99u8`
   - Expected: bytes[81] equals `114u8`
   - Expected: bytes[88] equals `224u8`
   - Expected: bytes[96] equals `32u8`
   - Expected: bytes[97] equals `0u8`
   - Expected: bytes[104] equals `30u8`
   - Expected: bytes[112] equals `2u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes the profile length/bytes and the three obligation counts at exact offsets")
val note = build_test_note()
val bytes = note.to_bytes()
# profile_len at offset 12 + 64 = 76
expect(bytes[76]).to_equal(8u8)   # len("critical") = 8
expect(bytes[77]).to_equal(0u8)
# profile bytes at offset 80: 'c'=99, 'r'=114
expect(bytes[80]).to_equal(99u8)
expect(bytes[81]).to_equal(114u8)
# build_timestamp_unix (u64 LE) at offset 80 + 8 = 88.
# 1754540000 mod 256 = 224 (1754540000 = 6853671*256 + 224).
expect(bytes[88]).to_equal(224u8)
# obligations_checked (u64 LE) at offset 96: value 32
expect(bytes[96]).to_equal(32u8)
expect(bytes[97]).to_equal(0u8)
# obligations_complied (u64 LE) at offset 104: value 30
expect(bytes[104]).to_equal(30u8)
# obligations_violated (u64 LE) at offset 112: value 2
expect(bytes[112]).to_equal(2u8)
```

</details>

#### normalizes the assurance profile name via WP-3's canonical table

- normalizes the assurance profile name via WP-3's canonical table
   - Expected: note.assurance_profile equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("normalizes the assurance profile name via WP-3's canonical table")
val note = AssuranceObjectNoteV1.create(
    "0000000000000000000000000000000000000000000000000000000000ab",
    "MISSION-CRITICAL",
    1,
    0,
    0,
    0
)
expect(note.assurance_profile).to_equal("critical")
```

</details>

### AssuranceObjectNoteV1 attaches to SmfWriter and appears in write() output

#### add_assurance_note_section wires real note bytes into the SMF image

- add_assurance_note_section wires real note bytes into the SMF image
   - Expected: result.is_ok() is true
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("add_assurance_note_section wires real note bytes into the SMF image")
var writer = SmfWriter.create()
writer.add_code_section("code", [195])
val note = build_test_note()
writer.add_assurance_note_section(note)
val result = writer.write()
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()

# The note payload (120 bytes, starting "AON1") must appear somewhere
# in the written image -- a genuine integration proof, not an
# isolated unit test of the struct alone.
var found = false
var i = 0
val note_bytes = note.to_bytes()
while i <= bytes.len() - note_bytes.len():
    if (bytes[i] == 65 and bytes[i + 1] == 79
            and bytes[i + 2] == 78 and bytes[i + 3] == 49):
        var matches = true
        var j = 0
        while j < note_bytes.len():
            if bytes[i + j] != (note_bytes[j] as i64):
                matches = false
            j = j + 1
        if matches:
            found = true
    i = i + 1
expect(found).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `706fe37db816d2d7bf290c52799b2ca32b95976e85e937ec99ee1ed462486380`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `706fe37db816d2d7bf290c52799b2ca32b95976e85e937ec99ee1ed462486380`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `706fe37db816d2d7bf290c52799b2ca32b95976e85e937ec99ee1ed462486380`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/linker/assurance_object_note_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/assurance_object_note_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/assurance_object_note_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/assurance_object_note_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/assurance_object_note_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/assurance_object_note_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces real, non-empty bytes with the expected total length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/assurance_object_note_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes the magic, version, hash length, and hash bytes at exact offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/assurance_object_note_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes the profile length/bytes and the three obligation counts at exact offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
