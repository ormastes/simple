# ripemd160_spec

> RIPEMD-160 Official Known-Answer Test Vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ripemd160_spec

RIPEMD-160 Official Known-Answer Test Vectors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/ripemd160_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

RIPEMD-160 Official Known-Answer Test Vectors.

Tests the pure-Simple RIPEMD-160 implementation in
src/os/crypto/ripemd160.spl against the 7 canonical vectors from the
RIPEMD-160 specification (Dobbertin, Bosselaers, Preneel 1996) and
ISO/IEC 10118-3.

Vectors covered (7):
  ""                                                -> 9c1185a5c5e9fc54612808977ee8f548b2258d31
  "a"                                               -> 0bdc9d2d256b3ee9daae347be6f4dc835a467ffe
  "abc"                                             -> 8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
  "message digest"                                  -> 5d0689ef49d2fae572b881b123a85ffa21595f36
  "abcdefghijklmnopqrstuvwxyz"                      -> f71c27109c692c1b56bbdceb5b9d2865b3708dbc
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
                                                    -> b0e20b6e3116640286ed3a87a5713079b21f5189
  "1234567890" repeated 8 times                     -> 9b752e45573d4b39f4dbd3323cab82bf63326bfb

Skipped (too slow in interpreter):
  1,000,000 × "a"                                   -> 52783243c1697bdbe16d37f97f68f08325dc1528

NOTE: interpreter-mode test runner verifies file loading only; it-block
assertions execute under compiled/native mode (feedback_compile_mode_false_greens).

## Scenarios

### RIPEMD-160 — official ISO/IEC 10118-3 known-answer vectors

#### empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty string
   - Expected: ripemd160_hex("") equals `9c1185a5c5e9fc54612808977ee8f548b2258d31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string")
# RIPEMD-160("") = 9c1185a5c5e9fc54612808977ee8f548b2258d31
expect(ripemd160_hex("")).to_equal("9c1185a5c5e9fc54612808977ee8f548b2258d31")
```

</details>

#### single character 'a'

- single character 'a'
   - Expected: ripemd160_hex("a") equals `0bdc9d2d256b3ee9daae347be6f4dc835a467ffe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single character 'a'")
# RIPEMD-160("a") = 0bdc9d2d256b3ee9daae347be6f4dc835a467ffe
expect(ripemd160_hex("a")).to_equal("0bdc9d2d256b3ee9daae347be6f4dc835a467ffe")
```

</details>

#### 'abc'

- 'abc'
   - Expected: ripemd160_hex("abc") equals `8eb208f7e05d987a9b044a8e98c6b087f15a0bfc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'abc'")
# RIPEMD-160("abc") = 8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
expect(ripemd160_hex("abc")).to_equal("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc")
```

</details>

#### 'message digest'

- 'message digest'
   - Expected: ripemd160_hex("message digest") equals `5d0689ef49d2fae572b881b123a85ffa21595f36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'message digest'")
# RIPEMD-160("message digest") = 5d0689ef49d2fae572b881b123a85ffa21595f36
expect(ripemd160_hex("message digest")).to_equal("5d0689ef49d2fae572b881b123a85ffa21595f36")
```

</details>

#### lowercase alphabet a-z

- lowercase alphabet a-z
   - Expected: ripemd160_hex("abcdefghijklmnopqrstuvwxyz") equals `f71c27109c692c1b56bbdceb5b9d2865b3708dbc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowercase alphabet a-z")
# RIPEMD-160("abcdefghijklmnopqrstuvwxyz") = f71c27109c692c1b56bbdceb5b9d2865b3708dbc
expect(ripemd160_hex("abcdefghijklmnopqrstuvwxyz")).to_equal("f71c27109c692c1b56bbdceb5b9d2865b3708dbc")
```

</details>

#### alphanumeric A-Z + a-z + 0-9

- alphanumeric A-Z + a-z + 0-9
   - Expected: ripemd160_hex(msg) equals `b0e20b6e3116640286ed3a87a5713079b21f5189`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alphanumeric A-Z + a-z + 0-9")
# RIPEMD-160("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789")
#   = b0e20b6e3116640286ed3a87a5713079b21f5189
val msg = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
expect(ripemd160_hex(msg)).to_equal("b0e20b6e3116640286ed3a87a5713079b21f5189")
```

</details>

#### '1234567890' repeated 8 times (80-byte input)

- '1234567890' repeated 8 times (80-byte input)
   - Expected: ripemd160_hex(_ten_digits_x8()) equals `9b752e45573d4b39f4dbd3323cab82bf63326bfb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'1234567890' repeated 8 times (80-byte input)")
# RIPEMD-160("12345678901234567890...") = 9b752e45573d4b39f4dbd3323cab82bf63326bfb
expect(ripemd160_hex(_ten_digits_x8())).to_equal("9b752e45573d4b39f4dbd3323cab82bf63326bfb")
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

- Canonical SPipe generation for source `8f45b2e52c78982f2e5782352c4f7e784bc0b4a5272ab80e6baf0f891e183431`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f45b2e52c78982f2e5782352c4f7e784bc0b4a5272ab80e6baf0f891e183431`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f45b2e52c78982f2e5782352c4f7e784bc0b4a5272ab80e6baf0f891e183431`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/ripemd160_spec.spl
mirror: doc/06_spec/unit/os/crypto/ripemd160_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/ripemd160_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/ripemd160_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/ripemd160_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/ripemd160_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single character 'a'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/ripemd160_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario ''abc'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
