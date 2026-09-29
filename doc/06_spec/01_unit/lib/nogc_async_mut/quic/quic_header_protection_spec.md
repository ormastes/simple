# quic_header_protection_spec

> QUIC AES header-protection mask spec (RFC 9001 §5.4.3 + Appendix A.2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# quic_header_protection_spec

QUIC AES header-protection mask spec (RFC 9001 §5.4.3 + Appendix A.2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

QUIC AES header-protection mask spec (RFC 9001 §5.4.3 + Appendix A.2).

quic_header_protect_mask is wired to the pure-Simple AES-128 block cipher
(AES-ECB of one block). Asserts the canonical RFC 9001 §A.2 Client Initial
header-protection vector: AES-ECB(hp, sample)[0..4] == 437b9aec36.

## Scenarios

### QUIC AES header protection (RFC 9001 §A.2)

#### produces a 5-byte mask

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a 5-byte mask
   - Expected: _mask_len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces a 5-byte mask")
expect(_mask_len()).to_equal(5)
```

</details>

#### mask[0] = 0x43

- mask[0] = 0x43
   - Expected: _mask_byte(0) equals `0x43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask[0] = 0x43")
expect(_mask_byte(0)).to_equal(0x43)
```

</details>

#### mask[1] = 0x7b

- mask[1] = 0x7b
   - Expected: _mask_byte(1) equals `0x7b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask[1] = 0x7b")
expect(_mask_byte(1)).to_equal(0x7b)
```

</details>

#### mask[2] = 0x9a

- mask[2] = 0x9a
   - Expected: _mask_byte(2) equals `0x9a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask[2] = 0x9a")
expect(_mask_byte(2)).to_equal(0x9a)
```

</details>

#### mask[3] = 0xec

- mask[3] = 0xec
   - Expected: _mask_byte(3) equals `0xec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask[3] = 0xec")
expect(_mask_byte(3)).to_equal(0xec)
```

</details>

#### mask[4] = 0x36

- mask[4] = 0x36
   - Expected: _mask_byte(4) equals `0x36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mask[4] = 0x36")
expect(_mask_byte(4)).to_equal(0x36)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d1c8732d7cf35c125f9f93c0db976b2c3e8535ee58028100cf38da4835bb2c4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1c8732d7cf35c125f9f93c0db976b2c3e8535ee58028100cf38da4835bb2c4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1c8732d7cf35c125f9f93c0db976b2c3e8535ee58028100cf38da4835bb2c4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a 5-byte mask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mask[0] = 0x43' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_header_protection_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mask[1] = 0x7b' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
