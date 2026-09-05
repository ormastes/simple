# avx512_abs_spec

> AVX-512 VPABSD/Q — byte-level emit golden tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_abs_spec

AVX-512 VPABSD/Q — byte-level emit golden tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx512_abs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

AVX-512 VPABSD/Q — byte-level emit golden tests

Tests emit_avx512_vpabsd and emit_avx512_vpabsq from
src/compiler/70.backend/backend/native/x86_64_avx512.spl
against Intel SDM Vol 2C §VPABSD/§VPABSQ encoding.
Register ID convention: zmm_to_index uses id-48, so zmm0=48, zmm1=49, etc.
Golden bytes verified via llvm-mc -triple=x86_64 -mattr=+avx512f --show-encoding.

## Scenarios

### AVX-512 VPABSD byte-level emit

#### VPABSD zmm0, zmm0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPABSD zmm0, zmm0
   - Expected: _list_hex(bytes) equals `62f27d481ec0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSD zmm0, zmm0")
val bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f27d481ec0")
```

</details>

#### VPABSD zmm1, zmm3

- VPABSD zmm1, zmm3
   - Expected: _list_hex(bytes) equals `62f27d481ecb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSD zmm1, zmm3")
val bytes = emit_avx512_vpabsd(X86_ZMM1, X86_ZMM3)
expect(_list_hex(bytes)).to_equal("62f27d481ecb")
```

</details>

#### VPABSD output length is 6 bytes

- VPABSD output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSD output length is 6 bytes")
val bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
expect(bytes.len()).to_equal(6)
```

</details>

### AVX-512 VPABSQ byte-level emit

#### VPABSQ zmm0, zmm0

- VPABSQ zmm0, zmm0
   - Expected: _list_hex(bytes) equals `62f2fd481ec0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSQ zmm0, zmm0")
val bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f2fd481ec0")
```

</details>

#### VPABSQ zmm2, zmm0

- VPABSQ zmm2, zmm0
   - Expected: _list_hex(bytes) equals `62f2fd481ed0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSQ zmm2, zmm0")
val bytes = emit_avx512_vpabsq(X86_ZMM2, X86_ZMM0)
expect(_list_hex(bytes)).to_equal("62f2fd481ed0")
```

</details>

#### VPABSQ output length is 6 bytes

- VPABSQ output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSQ output length is 6 bytes")
val bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPABSQ W-bit differs from VPABSD (byte index 2)

- VPABSQ W-bit differs from VPABSD (byte index 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPABSQ W-bit differs from VPABSD (byte index 2)")
val d_bytes = emit_avx512_vpabsd(X86_ZMM0, X86_ZMM0)
val q_bytes = emit_avx512_vpabsq(X86_ZMM0, X86_ZMM0)
expect(d_bytes[2]).to_not_equal(q_bytes[2])
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

- Canonical SPipe generation for source `9914a8590ca5450d14b74a9bcbec1a2b16a4bc6ae3f79369dbff7f5aa3dd27ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9914a8590ca5450d14b74a9bcbec1a2b16a4bc6ae3f79369dbff7f5aa3dd27ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9914a8590ca5450d14b74a9bcbec1a2b16a4bc6ae3f79369dbff7f5aa3dd27ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/backend/avx512_abs_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx512_abs_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx512_abs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx512_abs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx512_abs_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/avx512_abs_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPABSD zmm0, zmm0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_abs_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPABSD zmm1, zmm3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_abs_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPABSD output length is 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
