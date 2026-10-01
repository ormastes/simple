# streebog_kat_spec

> Streebog (GOST R 34.11-2012) Known-Answer Test Vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# streebog_kat_spec

Streebog (GOST R 34.11-2012) Known-Answer Test Vectors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/streebog_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Streebog (GOST R 34.11-2012) Known-Answer Test Vectors.

Tests the pure-Simple Streebog implementation in
src/os/crypto/streebog.spl against the canonical vectors from
RFC 6986 (the IETF publication of GOST R 34.11-2012).

Vectors used:

  Streebog-512("") =
      8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7
      362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a
  Source: gostcrypto reference implementation; first 8 bytes also appear
  in common Streebog-512("") references.  NOTE: RFC 6986 itself does not
  include an empty-string example; this vector is from independent
  cross-checked implementations.

  Streebog-512(M1) =
      1b54d01a4af5b9d5cc3d86d68d285462b19abc2475222f35c085122be4ba1ffa
      00ad30f8767b3a82384c6574f024c311e2a481332b08ef7f41797891c1646f48
  M1 = 63-byte ASCII "012345678901234567890123456789012345678901234567890123456789012"
  Source: RFC 6986 Appendix A.1.

  Streebog-256("") =
      3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb
  Source: RFC 6986 Appendix A.2, empty-string input.

NOTE: interpreter-mode test runner verifies file loading and basic
expressions; expect() assertions only fire under compiled/native mode
(see .claude/memory/feedback_compile_mode_false_greens.md).

## Scenarios

### Streebog-512 — RFC 6986 GOST R 34.11-2012 known-answer vectors

#### Streebog-512(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Streebog-512(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-512(\")
expect(_bytes_hex(streebog_512(_empty_bytes()))).to_equal(
    "8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a"
)
```

</details>

#### Streebog-512(M1) = 1b54d01a... (63-byte ASCII digit string)

- Streebog-512(M1) = 1b54d01a... (63-byte ASCII digit string)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-512(M1) = 1b54d01a... (63-byte ASCII digit string)")
expect(_bytes_hex(streebog_512(_m1_bytes()))).to_equal(
    "1b54d01a4af5b9d5cc3d86d68d285462b19abc2475222f35c085122be4ba1ffa00ad30f8767b3a82384c6574f024c311e2a481332b08ef7f41797891c1646f48"
)
```

</details>

#### Streebog-512 digest length is 64 bytes

- Streebog-512 digest length is 64 bytes
   - Expected: streebog_512(_empty_bytes()).len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-512 digest length is 64 bytes")
expect(streebog_512(_empty_bytes()).len()).to_equal(64)
```

</details>

#### Streebog-512(\

- Streebog-512(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-512(\")
val expected = "8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a"
assert_not_equal(_bytes_hex(streebog_512(_empty_bytes())), _reverse_hex_pairs(expected))
```

</details>

### Streebog-256 — RFC 6986 GOST R 34.11-2012 known-answer vectors

#### Streebog-256(\

- Streebog-256(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-256(\")
expect(_bytes_hex(streebog_256(_empty_bytes()))).to_equal(
    "3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb"
)
```

</details>

#### Streebog-256 digest length is 32 bytes

- Streebog-256 digest length is 32 bytes
   - Expected: streebog_256(_empty_bytes()).len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-256 digest length is 32 bytes")
expect(streebog_256(_empty_bytes()).len()).to_equal(32)
```

</details>

#### Streebog-256(\

- Streebog-256(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streebog-256(\")
val expected = "3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb"
assert_not_equal(_bytes_hex(streebog_256(_empty_bytes())), _reverse_hex_pairs(expected))
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `077599ecdccc9c57f612afb9c70c3202dd512f093c1744a9f86222a2e054d099`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `077599ecdccc9c57f612afb9c70c3202dd512f093c1744a9f86222a2e054d099`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `077599ecdccc9c57f612afb9c70c3202dd512f093c1744a9f86222a2e054d099`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/streebog_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/streebog_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/streebog_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/streebog_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/streebog_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/streebog_kat_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Streebog-512(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/streebog_kat_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Streebog-512(M1) = 1b54d01a... (63-byte ASCII digit string)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/streebog_kat_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Streebog-512 digest length is 64 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
