# smf_reader_spec

> SMF reader specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_reader_spec

SMF reader specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/linker/smf_reader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SMF reader specification tests.

## Scenarios

### Smf Reader

#### parses a raw header into the high-level header view

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a raw header into the high-level header view
   - Expected: header.version equals `(1, 1)`
   - Expected: header.platform equals `Platform.Linux`
   - Expected: header.arch equals `Arch.X86_64`
   - Expected: header.section_count equals `4`
   - Expected: header.symbol_count equals `6`
   - Expected: header.flags.executable is true
   - Expected: header.flags.debug_info is true
   - Expected: header.has_note_sdn is true
   - Expected: header.compression equals `CompressionType.Zstd`
   - Expected: header.is_v1_1() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a raw header into the high-level header view")
val raw = SmfHeaderRaw(
    magic: [83, 77, 70, 0],
    version_major: 1,
    version_minor: 1,
    platform: 1,
    arch: 0,
    flags: 0x01 | 0x04 | 0x20,
    compression: 1,
    section_count: 4,
    section_table_offset: 128,
    symbol_table_offset: 256,
    symbol_count: 6,
    exported_count: 2,
    entry_point: 4096,
    stub_size: 0,
    smf_data_offset: 128,
    module_hash: 123,
    source_hash: 456,
    app_type: 0
)

val header = SmfHeader.from_raw(raw)
expect(header.version).to_equal((1, 1))
expect(header.platform).to_equal(Platform.Linux)
expect(header.arch).to_equal(Arch.X86_64)
expect(header.section_count).to_equal(4)
expect(header.symbol_count).to_equal(6)
expect(header.flags.executable).to_equal(true)
expect(header.flags.debug_info).to_equal(true)
expect(header.has_note_sdn).to_equal(true)
expect(header.compression).to_equal(CompressionType.Zstd)
expect(header.is_v1_1()).to_equal(true)
```

</details>

#### maps platform, arch, and compression helper values

- maps platform, arch, and compression helper values
   - Expected: parse_platform(1).name() equals `linux`
   - Expected: parse_platform(99).name() equals `any`
   - Expected: parse_arch(0).name() equals `x86_64`
   - Expected: parse_arch(7).name() equals `wasm64`
   - Expected: parse_compression(0).name() equals `none`
   - Expected: parse_compression(2).name() equals `lz4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps platform, arch, and compression helper values")
expect(parse_platform(1).name()).to_equal("linux")
expect(parse_platform(99).name()).to_equal("any")
expect(parse_arch(0).name()).to_equal("x86_64")
expect(parse_arch(7).name()).to_equal("wasm64")
expect(parse_compression(0).name()).to_equal("none")
expect(parse_compression(2).name()).to_equal("lz4")
```

</details>

#### parses bit flags consistently

- parses bit flags consistently
   - Expected: flags.executable is true
   - Expected: flags.reloadable is true
   - Expected: flags.debug_info is false
   - Expected: flags.pic is true
   - Expected: flags.has_stub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bit flags consistently")
val flags = parse_flags(0x01 | 0x02 | 0x08 | 0x10)
expect(flags.executable).to_equal(true)
expect(flags.reloadable).to_equal(true)
expect(flags.debug_info).to_equal(false)
expect(flags.pic).to_equal(true)
expect(flags.has_stub).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdb74f290fec807c4fab899ecc6f33dbaef16339fcf4f77d40340d505e892250`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdb74f290fec807c4fab899ecc6f33dbaef16339fcf4f77d40340d505e892250`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdb74f290fec807c4fab899ecc6f33dbaef16339fcf4f77d40340d505e892250`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/linker/smf_reader_spec.spl
mirror: doc/06_spec/unit/compiler/linker/smf_reader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/linker/smf_reader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/linker/smf_reader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/linker/smf_reader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/linker/smf_reader_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a raw header into the high-level header view' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_reader_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps platform, arch, and compression helper values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_reader_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bit flags consistently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
