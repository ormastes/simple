# Avx512 Vpternlog Specification

> Tests covering AVX-512 VPTERNLOGD byte-level emit, AVX-512 VPTERNLOGQ byte-level emit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Vpternlog Specification

## Scenarios

### AVX-512 VPTERNLOGD byte-level emit

#### VPTERNLOGD zmm0,zmm0,zmm0,0xFF (all-ones)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPTERNLOGD zmm0,zmm0,zmm0,0xFF (all-ones)
   - Expected: _list_hex(bytes) equals `62f37d4825c0ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGD zmm0,zmm0,zmm0,0xFF (all-ones)")
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0xFF)
expect(_list_hex(bytes)).to_equal("62f37d4825c0ff")
```

</details>

#### VPTERNLOGD zmm1,zmm2,zmm3,0xAC (blend)

- VPTERNLOGD zmm1,zmm2,zmm3,0xAC (blend)
   - Expected: _list_hex(bytes) equals `62f36d4825cbac`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGD zmm1,zmm2,zmm3,0xAC (blend)")
val bytes = emit_avx512_vpternlogd(X86_ZMM1, X86_ZMM2, X86_ZMM3, 0xAC)
expect(_list_hex(bytes)).to_equal("62f36d4825cbac")
```

</details>

#### VPTERNLOGD zmm0,zmm1,zmm0,0x00 (zero)

- VPTERNLOGD zmm0,zmm1,zmm0,0x00 (zero)
   - Expected: _list_hex(bytes) equals `62f3754825c000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGD zmm0,zmm1,zmm0,0x00 (zero)")
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM1, X86_ZMM0, 0x00)
expect(_list_hex(bytes)).to_equal("62f3754825c000")
```

</details>

#### VPTERNLOGD zmm0,zmm0,zmm0,0x96 (XOR3)

- VPTERNLOGD zmm0,zmm0,zmm0,0x96 (XOR3)
   - Expected: _list_hex(bytes) equals `62f37d4825c096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGD zmm0,zmm0,zmm0,0x96 (XOR3)")
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(_list_hex(bytes)).to_equal("62f37d4825c096")
```

</details>

#### output length is 7 bytes (EVEX 4 + opcode 1 + ModRM 1 + imm8 1)

- output length is 7 bytes (EVEX 4 + opcode 1 + ModRM 1 + imm8 1)
   - Expected: bytes.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length is 7 bytes (EVEX 4 + opcode 1 + ModRM 1 + imm8 1)")
val bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0xFF)
expect(bytes.len()).to_equal(7)
```

</details>

### AVX-512 VPTERNLOGQ byte-level emit

#### VPTERNLOGQ zmm0,zmm0,zmm0,0x96 (XOR3, 64-bit)

- VPTERNLOGQ zmm0,zmm0,zmm0,0x96 (XOR3, 64-bit)
   - Expected: _list_hex(bytes) equals `62f3fd4825c096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGQ zmm0,zmm0,zmm0,0x96 (XOR3, 64-bit)")
val bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(_list_hex(bytes)).to_equal("62f3fd4825c096")
```

</details>

#### VPTERNLOGQ output length is 7 bytes

- VPTERNLOGQ output length is 7 bytes
   - Expected: bytes.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGQ output length is 7 bytes")
val bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(bytes.len()).to_equal(7)
```

</details>

#### VPTERNLOGQ W-bit differs from VPTERNLOGD (byte index 2)

- VPTERNLOGQ W-bit differs from VPTERNLOGD (byte index 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPTERNLOGQ W-bit differs from VPTERNLOGD (byte index 2)")
val d_bytes = emit_avx512_vpternlogd(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
val q_bytes = emit_avx512_vpternlogq(X86_ZMM0, X86_ZMM0, X86_ZMM0, 0x96)
expect(d_bytes[2]).to_not_equal(q_bytes[2])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx512_vpternlog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AVX-512 VPTERNLOGD byte-level emit, AVX-512 VPTERNLOGQ byte-level emit.
- AVX-512 VPTERNLOGD byte-level emit
- AVX-512 VPTERNLOGQ byte-level emit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `58c0029b947ebbf1cd89d30cdc69fec643bbe1dc2edab209388af23407a1cc16`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58c0029b947ebbf1cd89d30cdc69fec643bbe1dc2edab209388af23407a1cc16`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58c0029b947ebbf1cd89d30cdc69fec643bbe1dc2edab209388af23407a1cc16`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/backend/avx512_vpternlog_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx512_vpternlog_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx512_vpternlog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx512_vpternlog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx512_vpternlog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/avx512_vpternlog_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPTERNLOGD zmm0,zmm0,zmm0,0xFF (all-ones)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_vpternlog_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPTERNLOGD zmm1,zmm2,zmm3,0xAC (blend)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_vpternlog_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPTERNLOGD zmm0,zmm1,zmm0,0x00 (zero)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
