# smf_integration_spec

> SMF integration specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_integration_spec

SMF integration specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/linker/smf_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SMF integration specification tests.

## Scenarios

### Smf Integration

#### preserves key header fields through serialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves key header fields through serialization
   - Expected: bytes.len() equals `SMF_HEADER_SIZE`
   - Expected: bytes[0] equals `83`
   - Expected: bytes[1] equals `77`
   - Expected: bytes[2] equals `70`
   - Expected: bytes[3] equals `0`
   - Expected: bytes[4] equals `1`
   - Expected: bytes[5] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves key header fields through serialization")
var header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
header.set_executable(true)
header.set_reloadable(true)
header.section_count = 5
header.symbol_count = 10
header.exported_count = 3
header.entry_point = 0x1000
header.set_compression(CompressionType.Zstd, 3)
header.set_stub_info(1024, 1024)
header.set_app_type(SmfAppType.Tui)
header.set_window_hints(1024, 768)
header.set_prefetch_hint(true, 8)

val bytes = header.to_bytes()
expect(bytes.len()).to_equal(SMF_HEADER_SIZE)
expect(bytes[0]).to_equal(83)
expect(bytes[1]).to_equal(77)
expect(bytes[2]).to_equal(70)
expect(bytes[3]).to_equal(0)
expect(bytes[4]).to_equal(1)
expect(bytes[5]).to_equal(1)
```

</details>

#### round-trips enum values through u8 conversions

- round-trips enum values through u8 conversions
   - Expected: Platform.Any.to_u8() equals `0`
   - Expected: Platform.Linux.to_u8() equals `1`
   - Expected: Platform.Windows.to_u8() equals `2`
   - Expected: Platform.MacOS.to_u8() equals `3`
   - Expected: Platform.FreeBSD.to_u8() equals `4`
   - Expected: Platform.None_.to_u8() equals `5`
   - Expected: Arch.X86_64.to_u8() equals `0`
   - Expected: Arch.Aarch64.to_u8() equals `1`
   - Expected: Arch.X86.to_u8() equals `2`
   - Expected: Arch.Arm.to_u8() equals `3`
   - Expected: Arch.Riscv64.to_u8() equals `4`
   - Expected: Arch.Riscv32.to_u8() equals `5`
   - Expected: Arch.Wasm32.to_u8() equals `6`
   - Expected: Arch.Wasm64.to_u8() equals `7`
   - Expected: CompressionType.None_.to_u8() equals `0`
   - Expected: CompressionType.Zstd.to_u8() equals `1`
   - Expected: CompressionType.Lz4.to_u8() equals `2`
   - Expected: SmfAppType.Cli.to_u8() equals `0`
   - Expected: SmfAppType.Tui.to_u8() equals `1`
   - Expected: SmfAppType.Gui.to_u8() equals `2`
   - Expected: SmfAppType.Service.to_u8() equals `3`
   - Expected: SmfAppType.Repl.to_u8() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips enum values through u8 conversions")
expect(Platform.Any.to_u8()).to_equal(0)
expect(Platform.Linux.to_u8()).to_equal(1)
expect(Platform.Windows.to_u8()).to_equal(2)
expect(Platform.MacOS.to_u8()).to_equal(3)
expect(Platform.FreeBSD.to_u8()).to_equal(4)
expect(Platform.None_.to_u8()).to_equal(5)

expect(Arch.X86_64.to_u8()).to_equal(0)
expect(Arch.Aarch64.to_u8()).to_equal(1)
expect(Arch.X86.to_u8()).to_equal(2)
expect(Arch.Arm.to_u8()).to_equal(3)
expect(Arch.Riscv64.to_u8()).to_equal(4)
expect(Arch.Riscv32.to_u8()).to_equal(5)
expect(Arch.Wasm32.to_u8()).to_equal(6)
expect(Arch.Wasm64.to_u8()).to_equal(7)

expect(CompressionType.None_.to_u8()).to_equal(0)
expect(CompressionType.Zstd.to_u8()).to_equal(1)
expect(CompressionType.Lz4.to_u8()).to_equal(2)

expect(SmfAppType.Cli.to_u8()).to_equal(0)
expect(SmfAppType.Tui.to_u8()).to_equal(1)
expect(SmfAppType.Gui.to_u8()).to_equal(2)
expect(SmfAppType.Service.to_u8()).to_equal(3)
expect(SmfAppType.Repl.to_u8()).to_equal(4)
```

</details>

#### builds minimal and full-featured headers

- builds minimal and full-featured headers
   - Expected: minimal.to_bytes().len() equals `SMF_HEADER_SIZE`
   - Expected: minimal.is_executable() is false
   - Expected: minimal.is_compressed() is false
   - Expected: minimal.has_stub() is false
   - Expected: full.to_bytes().len() equals `SMF_HEADER_SIZE`
   - Expected: full.is_executable() is true
   - Expected: full.is_reloadable() is true
   - Expected: full.has_debug_info() is true
   - Expected: full.is_pic() is true
   - Expected: full.is_compressed() is true
   - Expected: full.has_stub() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds minimal and full-featured headers")
val minimal = SmfHeader.new_v1_1(Platform.Any, Arch.X86_64)
expect(minimal.to_bytes().len()).to_equal(SMF_HEADER_SIZE)
expect(minimal.is_executable()).to_equal(false)
expect(minimal.is_compressed()).to_equal(false)
expect(minimal.has_stub()).to_equal(false)

var full = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
full.set_executable(true)
full.set_reloadable(true)
full.set_debug_info(true)
full.set_pic(true)
full.set_compression(CompressionType.Zstd, 5)
full.set_stub_info(4096, 4096)
full.set_app_type(SmfAppType.Gui)
full.set_window_hints(1920, 1080)
full.set_prefetch_hint(true, 20)

expect(full.to_bytes().len()).to_equal(SMF_HEADER_SIZE)
expect(full.is_executable()).to_equal(true)
expect(full.is_reloadable()).to_equal(true)
expect(full.has_debug_info()).to_equal(true)
expect(full.is_pic()).to_equal(true)
expect(full.is_compressed()).to_equal(true)
expect(full.has_stub()).to_equal(true)
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

- Canonical SPipe generation for source `535f83760e2f0f4c7424ed93af6c2c26dd4e80397b5d9d4840ba39c76662e402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `535f83760e2f0f4c7424ed93af6c2c26dd4e80397b5d9d4840ba39c76662e402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `535f83760e2f0f4c7424ed93af6c2c26dd4e80397b5d9d4840ba39c76662e402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/linker/smf_integration_spec.spl
mirror: doc/06_spec/unit/compiler/linker/smf_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/linker/smf_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/linker/smf_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/linker/smf_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/linker/smf_integration_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves key header fields through serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_integration_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips enum values through u8 conversions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_integration_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds minimal and full-featured headers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
