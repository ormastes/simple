# encode_rvv_zvk_spec

> Purpose: Prove that encode_rvv_zvk — Zvkned AES instructions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# encode_rvv_zvk_spec

Purpose: Prove that encode_rvv_zvk — Zvkned AES instructions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/encode_rvv_zvk_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that encode_rvv_zvk — Zvkned AES instructions.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### encode_rvv_zvk — Zvkned AES instructions

#### emit_vaesef_vv vd=1 vs2=2 — AES final-round enc

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emit_vaesef_vv vd=1 vs2=2 — AES final-round enc
- Verify: emit_vaesef_vv vd=1 vs2=2 — AES final-round enc
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xA2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaesef_vv vd=1 vs2=2 — AES final-round enc")
step("Verify: emit_vaesef_vv vd=1 vs2=2 — AES final-round enc")
# @req: REQ-COMP-ENCODE-RVV-ZVK-ZVKNED-AES-INSTRUCTIONS-001
# funct6=0x28,vm=1,vs2=2,vs1=0,vd=1 → word=0xA22020D7
val got = emit_vaesef_vv(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xA2)
```

</details>

#### emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc

- emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc
- Verify: emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xA6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc")
step("Verify: emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc")
# funct6=0x29,vm=1,vs2=2,vs1=0,vd=1 → word=0xA62020D7
val got = emit_vaesem_vv(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xA6)
```

</details>

#### emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec

- emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec
- Verify: emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec")
step("Verify: emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec")
# funct6=0x2A,vm=1,vs2=2,vs1=0,vd=1 → word=0xAA2020D7
val got = emit_vaesdf_vv(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xAA)
```

</details>

#### emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec

- emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec
- Verify: emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xAE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec")
step("Verify: emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec")
# funct6=0x2B,vm=1,vs2=2,vs1=0,vd=1 → word=0xAE2020D7
val got = emit_vaesdm_vv(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xAE)
```

</details>

#### emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1

- emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1
- Verify: emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0x8A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1")
step("Verify: emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1")
# funct6=0x22,vm=1,vs2=2,vs1=2(uimm),vd=1 → word=0x8A2120D7
val got = emit_vaeskf1_vi(1, 2, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0x8A)
```

</details>

#### emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2

- emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2
- Verify: emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2")
step("Verify: emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2")
# funct6=0x2A,vm=1,vs2=2,vs1=2(uimm),vd=1 → word=0xAA2120D7
# NOTE: same funct6 as vaesdf.vv but vs1=2 (nonzero) distinguishes in context
val got = emit_vaeskf2_vi(1, 2, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0xAA)
```

</details>

#### emit_vaesz_vs vd=1 vs2=2 — AES round zero key

- emit_vaesz_vs vd=1 vs2=2 — AES round zero key
- Verify: emit_vaesz_vs vd=1 vs2=2 — AES round zero key
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vaesz_vs vd=1 vs2=2 — AES round zero key")
step("Verify: emit_vaesz_vs vd=1 vs2=2 — AES round zero key")
# funct6=0x2F,vm=1,vs2=2,vs1=0,vd=1 → word=0xBE2020D7
# NOTE: same funct6 as vsha2cl.vv but vs1=0 distinguishes in context
val got = emit_vaesz_vs(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xBE)
```

</details>

### encode_rvv_zvk — Zvknh SHA-2 instructions

#### emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule

- emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule
- Verify: emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0xA0`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0xB6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule")
step("Verify: emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule")
# funct6=0x2D,vm=1,vs2=2,vs1=3,vd=1 → word=0xB621A0D7
val got = emit_vsha2ms_vv(1, 2, 3)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0xA0)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0xB6)
```

</details>

#### emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high

- emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high
- Verify: emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0xA0`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0xBA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high")
step("Verify: emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high")
# funct6=0x2E,vm=1,vs2=2,vs1=3,vd=1 → word=0xBA21A0D7
val got = emit_vsha2ch_vv(1, 2, 3)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0xA0)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0xBA)
```

</details>

#### emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low

- emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low
- Verify: emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0xA0`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low")
step("Verify: emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low")
# funct6=0x2F,vm=1,vs2=2,vs1=3,vd=1 → word=0xBE21A0D7
# NOTE: same funct6 as vaesz.vs but vs1=3 (nonzero) distinguishes in context
val got = emit_vsha2cl_vv(1, 2, 3)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0xA0)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0xBE)
```

</details>

### encode_rvv_zvk — Zvkg GCM/GHASH instructions

#### emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc

- emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc
- Verify: emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0xA0`
   - Expected: got[2] equals `0x21`
   - Expected: got[3] equals `0xB2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc")
step("Verify: emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc")
# funct6=0x2C,vm=1,vs2=2,vs1=3,vd=1 → word=0xB221A0D7
val got = emit_vghsh_vv(1, 2, 3)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0xA0)
expect(got[2]).to_equal(0x21)
expect(got[3]).to_equal(0xB2)
```

</details>

#### emit_vgmul_vv vd=1 vs2=2 — GHASH multiply

- emit_vgmul_vv vd=1 vs2=2 — GHASH multiply
- Verify: emit_vgmul_vv vd=1 vs2=2 — GHASH multiply
   - Expected: got.length equals `4`
   - Expected: got[0] equals `0xD7`
   - Expected: got[1] equals `0x20`
   - Expected: got[2] equals `0x20`
   - Expected: got[3] equals `0xA6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_vgmul_vv vd=1 vs2=2 — GHASH multiply")
step("Verify: emit_vgmul_vv vd=1 vs2=2 — GHASH multiply")
# funct6=0x29,vm=1,vs2=2,vs1=0,vd=1 → word=0xA62020D7
# NOTE: same funct6 as vaesem.vv but vs1=0 distinguishes in context
val got = emit_vgmul_vv(1, 2)
expect(got.length).to_equal(4)
expect(got[0]).to_equal(0xD7)
expect(got[1]).to_equal(0x20)
expect(got[2]).to_equal(0x20)
expect(got[3]).to_equal(0xA6)
```

</details>

### encode_rvv_zvk — collision sanity checks

#### vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)

- vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)
- Verify: vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)
   - Expected: aesz[2] equals `0x20`
   - Expected: sha2cl[2] equals `0x21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)")
step("Verify: vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)")
# Both use funct6=0x2F; vs1 is in bits[19:15] -> byte[2]
# vaesz.vs  vs1=0: byte[2]=0x20
# vsha2cl.vv vs1=3: byte[2]=0x21 (little-endian byte 2 of 0xBE21A0D7)
val aesz = emit_vaesz_vs(1, 2)
val sha2cl = emit_vsha2cl_vv(1, 2, 3)
# vaesz_vs word=0xBE2020D7 → byte[2]=0x20
expect(aesz[2]).to_equal(0x20)
# vsha2cl_vv word=0xBE21A0D7 -> byte[2]=0x21 (vs1=3 sets bit16)
expect(sha2cl[2]).to_equal(0x21)
```

</details>

#### vaesem_vv and vgmul_vv produce same bytes when vs1=0

- vaesem_vv and vgmul_vv produce same bytes when vs1=0
- Verify: vaesem_vv and vgmul_vv produce same bytes when vs1=0
   - Expected: aesem[0] equals `vgmul[0]`
   - Expected: aesem[1] equals `vgmul[1]`
   - Expected: aesem[2] equals `vgmul[2]`
   - Expected: aesem[3] equals `vgmul[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vaesem_vv and vgmul_vv produce same bytes when vs1=0")
step("Verify: vaesem_vv and vgmul_vv produce same bytes when vs1=0")
# Both use funct6=0x29, vm=1, vs1=0; encoding is identical
# This is by spec design — disambiguated by ISA extension context
val aesem = emit_vaesem_vv(1, 2)
val vgmul = emit_vgmul_vv(1, 2)
expect(aesem[0]).to_equal(vgmul[0])
expect(aesem[1]).to_equal(vgmul[1])
expect(aesem[2]).to_equal(vgmul[2])
expect(aesem[3]).to_equal(vgmul[3])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-ENCODE-RVV-ZVK-ZVKNED-AES-INSTRUCTIONS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b71b30f9cbf759625e056ceff33b770d20f71e446026eb6a28bfcf311b71907`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b71b30f9cbf759625e056ceff33b770d20f71e446026eb6a28bfcf311b71907`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b71b30f9cbf759625e056ceff33b770d20f71e446026eb6a28bfcf311b71907`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/encode_rvv_zvk_spec.spl
mirror: doc/06_spec/unit/compiler/backend/encode_rvv_zvk_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/encode_rvv_zvk_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/encode_rvv_zvk_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/encode_rvv_zvk_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/encode_rvv_zvk_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_vaesef_vv vd=1 vs2=2 — AES final-round enc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/encode_rvv_zvk_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/encode_rvv_zvk_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
