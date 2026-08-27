# eth_fcs_spec

> Ethernet FCS (IEEE 802.3 CRC-32) synthesizable RTL core spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# eth_fcs_spec

Ethernet FCS (IEEE 802.3 CRC-32) synthesizable RTL core spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Ethernet FCS (IEEE 802.3 CRC-32) synthesizable RTL core spec.

Drives the combinational per-octet CRC step over test frames and asserts the
canonical CRC-32 known-answer vectors, plus the MAC receiver-side validation
(recomputed FCS matches the transmitted trailer).

## Scenarios

### Ethernet FCS CRC-32 RTL core (IEEE 802.3)

#### computes the canonical check value FCS(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes the canonical check value FCS(\
   - Expected: _fcs(_digits()) equals `0xCBF43926`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes the canonical check value FCS(\")
expect(_fcs(_digits())).to_equal(0xCBF43926)
```

</details>

#### FCS of the empty frame is 0

- FCS of the empty frame is 0
   - Expected: _fcs(empty) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("FCS of the empty frame is 0")
val empty: [u8] = []
expect(_fcs(empty)).to_equal(0)
```

</details>

#### FCS of single byte 'A' (0x41) = 0xD3D99E8B

- FCS of single byte 'A' (0x41) = 0xD3D99E8B
   - Expected: _fcs(a) equals `0xD3D99E8B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("FCS of single byte 'A' (0x41) = 0xD3D99E8B")
val a: [u8] = [0x41u8]
expect(_fcs(a)).to_equal(0xD3D99E8B)
```

</details>

#### distinct frames produce distinct FCS

- distinct frames produce distinct FCS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinct frames produce distinct FCS")
val other: [u8] = [0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x35u8, 0x36u8, 0x37u8, 0x38u8, 0x30u8]
assert_not_equal(_fcs(_digits()), _fcs(other))
```

</details>

#### receiver validation accepts a matching recomputed FCS

- receiver validation accepts a matching recomputed FCS
   - Expected: _check_roundtrip() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("receiver validation accepts a matching recomputed FCS")
expect(_check_roundtrip()).to_equal(true)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58f05888de9dd48d6985f7785bdcd31af0d560f595b092bfb2636ba83fd10c61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58f05888de9dd48d6985f7785bdcd31af0d560f595b092bfb2636ba83fd10c61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58f05888de9dd48d6985f7785bdcd31af0d560f595b092bfb2636ba83fd10c61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the canonical check value FCS(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FCS of the empty frame is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FCS of single byte 'A' (0x41) = 0xD3D99E8B' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
