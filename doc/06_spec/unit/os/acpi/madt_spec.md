# ACPI MADT Parser Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ACPI MADT Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/acpi/madt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### ACPI MADT parser

#### encodes APIC table signature little-endian

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes APIC table signature little-endian
   - Expected: ACPI_SIG_APIC equals `0x43495041`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes APIC table signature little-endian")
expect(ACPI_SIG_APIC).to_equal(0x43495041)
```

</details>

#### extracts enabled local APIC and online-capable x2APIC ids

- extracts enabled local APIC and online-capable x2APIC ids
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `2u32`
   - Expected: ids[1] equals `0x101u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts enabled local APIC and online-capable x2APIC ids")
val buf = _make_madt_fixture()
fn r8(off: u64) -> u8: _buf_read8(buf, off)
fn r32(off: u64) -> u32: _buf_read32(buf, off)

val ids = acpi_madt_lapic_ids_raw(r8, r32, 0u64)

expect(ids.len()).to_equal(2)
expect(ids[0]).to_equal(2u32)
expect(ids[1]).to_equal(0x101u32)
```

</details>

#### returns empty ids for undersized MADT

- returns empty ids for undersized MADT
   - Expected: ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty ids for undersized MADT")
val buf = _zero_buf(40u64)
val sized = _put_u32_le(buf, 4u64, 40u32)
fn r8(off: u64) -> u8: _buf_read8(sized, off)
fn r32(off: u64) -> u32: _buf_read32(sized, off)

val ids = acpi_madt_lapic_ids_raw(r8, r32, 0u64)

expect(ids.len()).to_equal(0)
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

- Canonical SPipe generation for source `5db03170a39b8959611fc7196ac3f2f8dcb38238245207b754b21649dff6fce2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5db03170a39b8959611fc7196ac3f2f8dcb38238245207b754b21649dff6fce2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5db03170a39b8959611fc7196ac3f2f8dcb38238245207b754b21649dff6fce2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/acpi/madt_spec.spl
mirror: doc/06_spec/unit/os/acpi/madt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/acpi/madt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/acpi/madt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/acpi/madt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/acpi/madt_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes APIC table signature little-endian' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/acpi/madt_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts enabled local APIC and online-capable x2APIC ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/acpi/madt_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty ids for undersized MADT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
