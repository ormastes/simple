# avx512_vpmov_spec

> Purpose: Prove that AVX-512 VPMOVZXBD byte-level emit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_vpmov_spec

Purpose: Prove that AVX-512 VPMOVZXBD byte-level emit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_vpmov_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 VPMOVZXBD byte-level emit.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 VPMOVZXBD byte-level emit

#### VPMOVZXBD zmm0, xmm0 — golden bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPMOVZXBD zmm0, xmm0 — golden bytes
- Verify: VPMOVZXBD zmm0, xmm0 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4831c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXBD zmm0, xmm0 — golden bytes")
step("Verify: VPMOVZXBD zmm0, xmm0 — golden bytes")
# @req: REQ-COMP-AVX-512-VPMOVZXBD-BYTE-LEVEL-EMIT-001
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4831c0")
```

</details>

#### VPMOVZXBD zmm1, xmm1 — golden bytes

- VPMOVZXBD zmm1, xmm1 — golden bytes
- Verify: VPMOVZXBD zmm1, xmm1 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4831c9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXBD zmm1, xmm1 — golden bytes")
step("Verify: VPMOVZXBD zmm1, xmm1 — golden bytes")
val bytes = emit_avx512_vpmovzxbd(X86_ZMM1, XMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4831c9")
```

</details>

#### VPMOVZXBD output length is 6 bytes

- VPMOVZXBD output length is 6 bytes
- Verify: VPMOVZXBD output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXBD output length is 6 bytes")
step("Verify: VPMOVZXBD output length is 6 bytes")
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVZXBD EVEX escape byte is 0x62

- VPMOVZXBD EVEX escape byte is 0x62
- Verify: VPMOVZXBD EVEX escape byte is 0x62
   - Expected: bytes[0] equals `0x62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXBD EVEX escape byte is 0x62")
step("Verify: VPMOVZXBD EVEX escape byte is 0x62")
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[0]).to_equal(0x62)
```

</details>

#### VPMOVZXBD opcode byte is 0x31

- VPMOVZXBD opcode byte is 0x31
- Verify: VPMOVZXBD opcode byte is 0x31
   - Expected: bytes[4] equals `0x31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXBD opcode byte is 0x31")
step("Verify: VPMOVZXBD opcode byte is 0x31")
val bytes = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[4]).to_equal(0x31)
```

</details>

### AVX-512 VPMOVZXWD byte-level emit

#### VPMOVZXWD zmm0, ymm0 — golden bytes

- VPMOVZXWD zmm0, ymm0 — golden bytes
- Verify: VPMOVZXWD zmm0, ymm0 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4833c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXWD zmm0, ymm0 — golden bytes")
step("Verify: VPMOVZXWD zmm0, ymm0 — golden bytes")
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4833c0")
```

</details>

#### VPMOVZXWD zmm1, ymm1 — golden bytes

- VPMOVZXWD zmm1, ymm1 — golden bytes
- Verify: VPMOVZXWD zmm1, ymm1 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4833c9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXWD zmm1, ymm1 — golden bytes")
step("Verify: VPMOVZXWD zmm1, ymm1 — golden bytes")
val bytes = emit_avx512_vpmovzxwd(X86_ZMM1, YMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4833c9")
```

</details>

#### VPMOVZXWD output length is 6 bytes

- VPMOVZXWD output length is 6 bytes
- Verify: VPMOVZXWD output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXWD output length is 6 bytes")
step("Verify: VPMOVZXWD output length is 6 bytes")
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVZXWD opcode byte is 0x33

- VPMOVZXWD opcode byte is 0x33
- Verify: VPMOVZXWD opcode byte is 0x33
   - Expected: bytes[4] equals `0x33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVZXWD opcode byte is 0x33")
step("Verify: VPMOVZXWD opcode byte is 0x33")
val bytes = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bytes[4]).to_equal(0x33)
```

</details>

### AVX-512 VPMOVSXBD byte-level emit

#### VPMOVSXBD zmm0, xmm0 — golden bytes

- VPMOVSXBD zmm0, xmm0 — golden bytes
- Verify: VPMOVSXBD zmm0, xmm0 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4821c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXBD zmm0, xmm0 — golden bytes")
step("Verify: VPMOVSXBD zmm0, xmm0 — golden bytes")
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4821c0")
```

</details>

#### VPMOVSXBD zmm1, xmm1 — golden bytes

- VPMOVSXBD zmm1, xmm1 — golden bytes
- Verify: VPMOVSXBD zmm1, xmm1 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4821c9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXBD zmm1, xmm1 — golden bytes")
step("Verify: VPMOVSXBD zmm1, xmm1 — golden bytes")
val bytes = emit_avx512_vpmovsxbd(X86_ZMM1, XMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4821c9")
```

</details>

#### VPMOVSXBD output length is 6 bytes

- VPMOVSXBD output length is 6 bytes
- Verify: VPMOVSXBD output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXBD output length is 6 bytes")
step("Verify: VPMOVSXBD output length is 6 bytes")
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVSXBD opcode byte is 0x21

- VPMOVSXBD opcode byte is 0x21
- Verify: VPMOVSXBD opcode byte is 0x21
   - Expected: bytes[4] equals `0x21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXBD opcode byte is 0x21")
step("Verify: VPMOVSXBD opcode byte is 0x21")
val bytes = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(bytes[4]).to_equal(0x21)
```

</details>

### AVX-512 VPMOVSXWD byte-level emit

#### VPMOVSXWD zmm0, ymm0 — golden bytes

- VPMOVSXWD zmm0, ymm0 — golden bytes
- Verify: VPMOVSXWD zmm0, ymm0 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4823c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXWD zmm0, ymm0 — golden bytes")
step("Verify: VPMOVSXWD zmm0, ymm0 — golden bytes")
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4823c0")
```

</details>

#### VPMOVSXWD zmm1, ymm1 — golden bytes

- VPMOVSXWD zmm1, ymm1 — golden bytes
- Verify: VPMOVSXWD zmm1, ymm1 — golden bytes
   - Expected: _list_hex(bytes) equals `62f27d4823c9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXWD zmm1, ymm1 — golden bytes")
step("Verify: VPMOVSXWD zmm1, ymm1 — golden bytes")
val bytes = emit_avx512_vpmovsxwd(X86_ZMM1, YMM1_IDX)
expect(_list_hex(bytes)).to_equal("62f27d4823c9")
```

</details>

#### VPMOVSXWD output length is 6 bytes

- VPMOVSXWD output length is 6 bytes
- Verify: VPMOVSXWD output length is 6 bytes
   - Expected: bytes.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXWD output length is 6 bytes")
step("Verify: VPMOVSXWD output length is 6 bytes")
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bytes.len()).to_equal(6)
```

</details>

#### VPMOVSXWD opcode byte is 0x23

- VPMOVSXWD opcode byte is 0x23
- Verify: VPMOVSXWD opcode byte is 0x23
   - Expected: bytes[4] equals `0x23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPMOVSXWD opcode byte is 0x23")
step("Verify: VPMOVSXWD opcode byte is 0x23")
val bytes = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bytes[4]).to_equal(0x23)
```

</details>

### AVX-512 VPMOV opcode differentiation

#### zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)

- zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)
- Verify: zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)
   - Expected: zx[0] equals `sx[0]`
   - Expected: zx[1] equals `sx[1]`
   - Expected: zx[2] equals `sx[2]`
   - Expected: zx[3] equals `sx[3]`
   - Expected: zx[5] equals `sx[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)")
step("Verify: zero-extend vs sign-extend BD differ only in opcode byte (byte index 4)")
val zx = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
val sx = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
expect(zx[0]).to_equal(sx[0])
expect(zx[1]).to_equal(sx[1])
expect(zx[2]).to_equal(sx[2])
expect(zx[3]).to_equal(sx[3])
expect(zx[4]).to_not_equal(sx[4])
expect(zx[5]).to_equal(sx[5])
```

</details>

#### zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)

- zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)
- Verify: zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)
   - Expected: zx[0] equals `sx[0]`
   - Expected: zx[1] equals `sx[1]`
   - Expected: zx[2] equals `sx[2]`
   - Expected: zx[3] equals `sx[3]`
   - Expected: zx[5] equals `sx[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)")
step("Verify: zero-extend vs sign-extend WD differ only in opcode byte (byte index 4)")
val zx = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
val sx = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(zx[0]).to_equal(sx[0])
expect(zx[1]).to_equal(sx[1])
expect(zx[2]).to_equal(sx[2])
expect(zx[3]).to_equal(sx[3])
expect(zx[4]).to_not_equal(sx[4])
expect(zx[5]).to_equal(sx[5])
```

</details>

#### BD vs WD zero-extend differ only in opcode byte (byte index 4)

- BD vs WD zero-extend differ only in opcode byte (byte index 4)
- Verify: BD vs WD zero-extend differ only in opcode byte (byte index 4)
   - Expected: bd[0] equals `wd[0]`
   - Expected: bd[1] equals `wd[1]`
   - Expected: bd[2] equals `wd[2]`
   - Expected: bd[3] equals `wd[3]`
   - Expected: bd[5] equals `wd[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BD vs WD zero-extend differ only in opcode byte (byte index 4)")
step("Verify: BD vs WD zero-extend differ only in opcode byte (byte index 4)")
val bd = emit_avx512_vpmovzxbd(X86_ZMM0, XMM0_IDX)
val wd = emit_avx512_vpmovzxwd(X86_ZMM0, YMM0_IDX)
expect(bd[0]).to_equal(wd[0])
expect(bd[1]).to_equal(wd[1])
expect(bd[2]).to_equal(wd[2])
expect(bd[3]).to_equal(wd[3])
expect(bd[4]).to_not_equal(wd[4])
expect(bd[5]).to_equal(wd[5])
```

</details>

#### BD vs WD sign-extend differ only in opcode byte (byte index 4)

- BD vs WD sign-extend differ only in opcode byte (byte index 4)
- Verify: BD vs WD sign-extend differ only in opcode byte (byte index 4)
   - Expected: bd[0] equals `wd[0]`
   - Expected: bd[1] equals `wd[1]`
   - Expected: bd[2] equals `wd[2]`
   - Expected: bd[3] equals `wd[3]`
   - Expected: bd[5] equals `wd[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BD vs WD sign-extend differ only in opcode byte (byte index 4)")
step("Verify: BD vs WD sign-extend differ only in opcode byte (byte index 4)")
val bd = emit_avx512_vpmovsxbd(X86_ZMM0, XMM0_IDX)
val wd = emit_avx512_vpmovsxwd(X86_ZMM0, YMM0_IDX)
expect(bd[0]).to_equal(wd[0])
expect(bd[1]).to_equal(wd[1])
expect(bd[2]).to_equal(wd[2])
expect(bd[3]).to_equal(wd[3])
expect(bd[4]).to_not_equal(wd[4])
expect(bd[5]).to_equal(wd[5])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-AVX-512-VPMOVZXBD-BYTE-LEVEL-EMIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e40d55a79b4cab068c0c0aca172f2bc552c7290614d5707206eed0fef4e34d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e40d55a79b4cab068c0c0aca172f2bc552c7290614d5707206eed0fef4e34d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e40d55a79b4cab068c0c0aca172f2bc552c7290614d5707206eed0fef4e34d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/avx512_vpmov_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/avx512_vpmov_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/avx512_vpmov_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/avx512_vpmov_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/avx512_vpmov_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/avx512_vpmov_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPMOVZXBD zmm0, xmm0 — golden bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_vpmov_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPMOVZXBD zmm1, xmm1 — golden bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_vpmov_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPMOVZXBD output length is 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
