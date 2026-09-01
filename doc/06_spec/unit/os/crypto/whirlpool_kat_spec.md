# whirlpool_kat_spec

> Whirlpool NESSIE Known-Answer Test Vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# whirlpool_kat_spec

Whirlpool NESSIE Known-Answer Test Vectors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/whirlpool_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Whirlpool NESSIE Known-Answer Test Vectors.

Tests the pure-Simple Whirlpool implementation in
src/os/crypto/whirlpool.spl against the three canonical NESSIE final
vectors (2003).

Vectors:
  Whirlpool("")    = 19fa61d75522a4669b44e39c1d2e1726c530232130d407f89afee0964997f7a7
                     3e83be698b288febcf88e3e03c4f0757ea8964e59b63d93708b138cc42a66eb3
  Whirlpool("a")   = 8aca2602792aec6f11a67206531fb7d7f0dff59413145e6973c45001d0087b42
                     d11bc645413aeff63a42391a39145a591a92200d560195e53b478584fdae231a
  Whirlpool("abc") = 4e2448a4c6f486bb16b6562c73b4020bf3043e3a731bce721ae1b303d97e6d4c
                     7181eebdb6c57e277d0e34957114cbd6c797fc9d95d8b582d225292076d4eef5

Source: NESSIE Whirlpool submission v3.0 / ISO/IEC 10118-3:2004 §13.

NOTE: interpreter-mode test runner verifies file loading and basic
expressions; expect() assertions only fire under compiled/native mode
(see .claude/memory/feedback_compile_mode_false_greens.md).

## Scenarios

### Whirlpool — NESSIE final known-answer vectors

#### Whirlpool(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Whirlpool(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Whirlpool(\")
expect(_bytes_hex(whirlpool(_empty_bytes()))).to_equal(
    "19fa61d75522a4669b44e39c1d2e1726c530232130d407f89afee0964997f7a73e83be698b288febcf88e3e03c4f0757ea8964e59b63d93708b138cc42a66eb3"
)
```

</details>

#### Whirlpool(\

- Whirlpool(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Whirlpool(\")
expect(_bytes_hex(whirlpool(_a_bytes()))).to_equal(
    "8aca2602792aec6f11a67206531fb7d7f0dff59413145e6973c45001d0087b42d11bc645413aeff63a42391a39145a591a92200d560195e53b478584fdae231a"
)
```

</details>

#### Whirlpool(\

- Whirlpool(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Whirlpool(\")
expect(_bytes_hex(whirlpool(_abc_bytes()))).to_equal(
    "4e2448a4c6f486bb16b6562c73b4020bf3043e3a731bce721ae1b303d97e6d4c7181eebdb6c57e277d0e34957114cbd6c797fc9d95d8b582d225292076d4eef5"
)
```

</details>

#### Whirlpool digest length is 64 bytes

- Whirlpool digest length is 64 bytes
   - Expected: whirlpool(_abc_bytes()).len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Whirlpool digest length is 64 bytes")
expect(whirlpool(_abc_bytes()).len()).to_equal(64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `2399561b3fb97668eeb1e065d356d28af549aa34a36b96a21b6a8d15e1eb6d55`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2399561b3fb97668eeb1e065d356d28af549aa34a36b96a21b6a8d15e1eb6d55`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2399561b3fb97668eeb1e065d356d28af549aa34a36b96a21b6a8d15e1eb6d55`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/whirlpool_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/whirlpool_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/whirlpool_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/whirlpool_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/whirlpool_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/whirlpool_kat_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Whirlpool(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/whirlpool_kat_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Whirlpool(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/whirlpool_kat_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Whirlpool(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
