<!-- claude-arch -->
# Architecture: SIMD Strict-Emit Errata

**TL;DR:** This document records confirmed bugs in the `evex_encode_3op_zmm` pseudocode in
`simd_backend_strict_emit_detail_part1.md` (C3a) §3.2. Two distinct bit-placement errors make
the function produce incorrect EVEX byte streams for **all** AVX-512 instructions — not merely
W=1 (f64) encodings as D1 V-06 initially characterized. The golden fixtures in C3b §10.3
(Fixture A-1) that D1's V-06 marked "byte sequence confirmed correct" must be treated as
**unverified**: a direct trace of C3a's pseudocode against the Intel SDM Vol 2A §2.6.1 layout
produces `62 F8 F5 C9 A8 C2`, not the claimed `62 F2 75 C9 A8 C2`. Corrected encoder
pseudocode and worked examples for VFMADD213PS (W=0) and VFMADD213PD (W=1) are provided
below. The M1 backend MUST NOT wire through `evex_encode_3op_zmm` as written; it must use the
corrected construction shown in ERR-001 §"Corrected byte-construction sequence". See also
`simd_spec_verification_2026-05-02.md` (D1) §V-01 and §V-06 for the verification context.

---

## Errata index

| ID | Source doc + section | Severity | Status | Affected goldens |
|---|---|---|---|---|
| ERR-001a | `simd_backend_strict_emit_detail_part1.md` §3.2 line 510 | CRITICAL (all EVEX goldens wrong) | RESOLVED | All AVX-512 EVEX goldens in C3b §10.3 |
| ERR-001b | `simd_backend_strict_emit_detail_part1.md` §3.2 lines 512, 516 | HIGH (W=1 f64 instructions decode as wrong map) | RESOLVED | All AVX-512 W=1 (f64/i64) EVEX goldens |
| ERR-001c | `simd_spec_verification_2026-05-02.md` §V-06 | LOW (doc error, not code) | OPEN | D1 V-06 "byte sequence confirmed correct" claim is wrong |

## Resolution log

| ERR | Resolved-in commit | Status | Notes |
|---|---|---|---|
| ERR-001a | (this commit) | RESOLVED in C3a §3 | Buggy `(mm & 3) << 2` mm-shift replaced with `(mm & 7) << 0`; mm bits[2:0] now land at correct P0 positions per Intel SDM Vol 2A §2.6.1 Table 2-36 |
| ERR-001b | (this commit) | RESOLVED in C3a §3 | Misplaced `w & 1` removed from P0; P1 bit[7] changed from hard-coded `1 << 7` to `(w & 1) << 7`; W now in correct Byte2 position per Intel SDM Vol 2A §2.6.1 |
| ERR-001c | — | OPEN | D1 V-06 doc claim not modified; requires separate doc errata in simd_spec_verification_2026-05-02.md |

Verified corrected output (canonical worked examples added to C3a §3.4):
- VFMADD213PS (f32, W=0): `62 F2 75 C9 A8 C2` — matches Intel SDM Vol 2B §4 VFMADD132/213/231PS
- VFMADD213PD (f64, W=1): `62 F2 F5 C9 A8 C2` — matches Intel SDM Vol 2B §4 VFMADD132/213/231PD

M1 emitter contract now references the post-fix pseudocode in C3a §3.2. ERR-001c (D1 V-06 doc claim) remains OPEN — it is a separate documentation correction outside F4's scope.

---

ERR-001a and ERR-001b are two independent bugs within the same function; both must be fixed
together. They are listed separately because they have different scope: 001a corrupts every
invocation, 001b is an additional corruption that only manifests when W=1.

---

## ERR-001 — EVEX P0 opcode-map shift error + W-bit misplacement

### Symptom

When any AVX-512 instruction is emitted through `evex_encode_3op_zmm` as written in C3a §3.2,
the resulting EVEX Byte1 (P0) has incorrect opcode-map bits and may carry the W-bit in the
wrong position. For VFMADD213PS (W=0, MAP2): the encoder emits `62 F8 F5 C9 A8 C2` but the
correct Intel-SDM-derived encoding is `62 F2 75 C9 A8 C2`. The CPU (or a disassembler) will
misinterpret the opcode-map field and may raise an invalid-instruction fault, execute the wrong
opcode, or — for MAP-adjacent instructions — silently compute wrong results.

### Root cause

C3a §3.2, lines 506–519 (reproduced for reference):

```
# Lines 506–512: P0 construction
p0 = ((~r_bit   & 1) << 7)
   | ((~x_bit   & 1) << 6)
   | ((~b_bit   & 1) << 5)
   | ((~r_prime & 1) << 4)
   | ((mm & 3)       << 2)   # <-- BUG ERR-001a (line 510)
   | (0              << 1)   # reserved 0
   | (w & 1)                 # <-- BUG ERR-001b (line 512)

# Lines 516–519: P1 construction
p1 = (1              << 7)   # <-- BUG ERR-001b (line 516): should be (w & 1) << 7
   | ((~vvvv_lo4 & 0xF) << 3)
   | (1              << 2)
   | (pp & 3)
```

**ERR-001a (line 510):** Intel SDM Vol 2A §2.6.1 Table 2-36 places the opcode-map bits at
Byte1 positions `[2]=m2, [1]=m1, [0]=m0`. C3a writes `(mm & 3) << 2`, which:
- Masks `mm` to only 2 bits, losing MAP5 (`101`) and MAP6 (`110`).
- Shifts those 2 bits to positions `[3:2]`, landing `m1` on the reserved-must-be-0 bit `[3]`
  and `m0` at bit `[2]` — while the actual `m2`, `m1`, `m0` positions `[2:0]` receive zero.

For mm=2 (MAP2 = 0F38 map, used by VFMADD213PS and VFMADD213PD):
- Correct: `m2=0, m1=1, m0=0` → bits[2:0] = `010`
- C3a produces: `(2 & 3) << 2 = 0x08` → bit[3]=1, bits[2:0]=0 → `mm_eff=000` (reserved map)
  plus the reserved bit 3 is set to 1, which is unconditionally invalid per Intel SDM §2.6.1.

**ERR-001b (lines 512 + 516):** Intel SDM Vol 2A §2.6.1 places the W-bit at Byte2 (P1) bit[7].
C3a places `w & 1` at Byte1 (P0) bit[0] (the m0 position) and puts the hard-coded `1 << 7`
into Byte2's must-be-1 location. Consequences:
- W is absent from Byte2 bit[7] — that field reads as 0 (W=0, f32) regardless of the `w`
  parameter.
- For W=0 instructions, the leaked W=0 at P0[0] does not visibly collide with the ERR-001a
  damage because m0 is already wrong for other reasons.
- For W=1 instructions (f64, i64), the leaked W=1 sets P0[0]=1, adding `m0=1` on top of the
  ERR-001a shift damage: effective mm becomes `001` (MAP1 = legacy `0F` escape) instead of
  `010` (MAP2 = `0F38`). The instruction decodes in the wrong opcode map.

### Why D1 V-06 over-stated the finding

D1's `simd_spec_verification_2026-05-02.md` §V-06 states "All 6 bytes `62 F2 75 C9 A8 C2`
are correct" and frames the encoder defect as a "P0/P1 label swap" that "two errors cancel"
for W=0. This characterization is **inaccurate**:

1. C3a does not produce `62 F2 75 C9 A8 C2` for the inputs (dest=0, src1=1, src2=2, k=1,
   z=true, mm=2, w=0, pp=1, opc=0xA8) — a direct trace of lines 506–536 yields `62 F8 F5 C9 A8 C2`.
2. There is no two-error cancellation. The two bugs (ERR-001a, ERR-001b) corrupt different bit
   fields and compound rather than cancel.
3. D1's conclusion that "Fixture A-1 byte sequence is canonical and correct" is true for the
   Intel-SDM-derived target bytes (`62 F2 75 C9 A8 C2`), but is not evidence that C3a can
   produce them — it cannot, in its current form.

C3a §3.2 must be treated as containing the bugs described above. D1 V-06 provides useful
discovery context; readers should weight the per-byte SDM decode table in V-06 as authoritative
and disregard the "two-error cancel" conclusion.

### Corrected byte-construction sequence

Corrected pseudocode for `evex_encode_3op_zmm`, per Intel SDM Vol 2A §2.6.1 Table 2-36:

```
fn evex_encode_3op_zmm(
    dest: i32, src1: i32, src2: i32,
    k_mask: i32, zeroing: bool,
    mm: i32,    # opcode map: 1=0F, 2=0F38, 3=0F3A, 5=MAP5, 6=MAP6
    w: i32,     # W bit: 0=f32/i32  1=f64/i64
    pp: i32,    # prefix: 0=none 1=0x66 2=0xF3 3=0xF2
    opcode: i32
) -> [u8; 6]:
    r_bit   = (dest  >> 3) & 1
    r_prime = (dest  >> 4) & 1
    x_bit   = 0              # no SIB for reg-reg
    b_bit   = (src2  >> 3) & 1

    # Byte1 (Intel SDM P0): ~R ~X ~B ~R' 0 m2 m1 m0
    # Intel SDM Vol 2A §2.6.1 Table 2-36: mm at bits[2:0], NO W here
    p0 = ((~r_bit   & 1) << 7)
       | ((~x_bit   & 1) << 6)
       | ((~b_bit   & 1) << 5)
       | ((~r_prime & 1) << 4)
       | (0               << 3)   # reserved, must be 0
       | (((mm >> 2) & 1) << 2)   # m2
       | (((mm >> 1) & 1) << 1)   # m1
       | ((mm >> 0) & 1)          # m0

    # Byte2 (Intel SDM P1): W ~v3 ~v2 ~v1 ~v0 1 p1 p0
    # Intel SDM Vol 2A §2.6.1 Table 2-36: W at bit[7]
    vvvv_lo4 = src1 & 0xF
    p1 = ((w & 1)            << 7)   # W at bit[7]  (CORRECTED)
       | ((~vvvv_lo4 & 0xF)  << 3)
       | (1                  << 2)   # must-1 (EVEX distinguisher)
       | (pp & 3)

    # Byte3 (Intel SDM P2): z L' L b ~V' a2 a1 a0  (unchanged)
    v_prime = (src1 >> 4) & 1
    z_bit   = if zeroing then 1 else 0
    ll      = 2       # 10 = 512-bit ZMM
    b_p2    = 0       # no broadcast/SAE for basic 3-op
    p2 = (z_bit          << 7)
       | (ll              << 5)
       | (b_p2            << 4)
       | ((~v_prime & 1)  << 3)
       | (k_mask & 7)

    modrm = (3 << 6) | ((dest & 7) << 3) | (src2 & 7)
    return [0x62, p0, p1, p2, opcode & 0xFF, modrm]
```

### Worked example: f32 VFMADD213PS (W=0)

**Instruction:** `VFMADD213PS zmm0{k1}{z}, zmm1, zmm2`
**Encoding form:** `EVEX.512.66.0F38.W0 A8 /r`
**Parameters:** dest=0, src1=1, src2=2, k=1, z=true, mm=2, w=0, pp=1, opc=0xA8

Corrected construction (per Intel SDM Vol 2A §2.6.1):
```
Byte0: 0x62  mandatory EVEX escape

Byte1 (P0 = 0xF2 = 1111_0010b):
  [7]=1  ~R=1  R=0  dest=zmm0 (idx<8)
  [6]=1  ~X=1  X=0  no SIB index
  [5]=1  ~B=1  B=0  src2=zmm2 (idx<8)
  [4]=1  ~R'=1 R'=0 dest<zmm16
  [3]=0  reserved=0
  [2]=0  m2=0
  [1]=1  m1=1   \  mm[2:0]=010 = MAP2 (0F38)
  [0]=0  m0=0   /

Byte2 (P1 = 0x75 = 0111_0101b):
  [7]=0  W=0   single-precision f32
  [6]=1  ~v3=1 v3=0
  [5]=1  ~v2=1 v2=0
  [4]=1  ~v1=1 v1=0
  [3]=0  ~v0=0 v0=1  vvvv=0001b = zmm1
  [2]=1  must-1
  [1]=0  pp[1]=0
  [0]=1  pp[0]=1  pp=01 = 0x66 prefix

Byte3 (P2 = 0xC9 = 1100_1001b):
  [7]=1  z=1   zeroing masking
  [6]=1  L'=1
  [5]=0  L=0   L'L=10 = 512-bit ZMM
  [4]=0  b=0   no broadcast/SAE
  [3]=1  ~V'=1 V'=0 vvvv<zmm16
  [2:0]=001 aaa=001 = k1 opmask

Byte4: 0xA8  opcode (VFMADD213PS in MAP2)
Byte5: 0xC2  ModRM: mod=11 reg=0(zmm0) rm=2(zmm2)

RESULT: 62 F2 75 C9 A8 C2  (matches Intel SDM Vol 2B §4 VFMADD132/213/231PS entry)
```

Buggy C3a encoder (lines 506–536 as written) produces: `62 F8 F5 C9 A8 C2`
- P0=0xF8 (`1111_1000`): mm bits[3:2]=`10`, bits[2:0]=`000` → wrong map, reserved bit set
- P1=0xF5 (`1111_0101`): W=1 at bit[7] (wrong — W=0 for this instruction)

### Worked example: f64 VFMADD213PD (W=1)

**Instruction:** `VFMADD213PD zmm0{k1}{z}, zmm1, zmm2`
**Encoding form:** `EVEX.512.66.0F38.W1 A8 /r`
**Parameters:** dest=0, src1=1, src2=2, k=1, z=true, mm=2, w=1, pp=1, opc=0xA8

Corrected construction (per Intel SDM Vol 2A §2.6.1):
```
Byte0: 0x62

Byte1 (P0 = 0xF2 = 1111_0010b):
  Same as f32: R/X/B/R' + mm=010=MAP2
  Note: W does NOT appear here — identical Byte1 for W=0 and W=1

Byte2 (P1 = 0xF5 = 1111_0101b):
  [7]=1  W=1   double-precision f64    (CHANGED from f32)
  [6:3]  ~vvvv = 1110b (same zmm1 source)
  [2]=1  must-1
  [1:0]  pp=01 = 0x66 prefix

Byte3: 0xC9  (same as f32)
Byte4: 0xA8  (same opcode, different W in prefix selects pd variant)
Byte5: 0xC2  (same ModRM)

RESULT: 62 F2 F5 C9 A8 C2
```

Buggy C3a encoder produces: `62 F9 F5 C9 A8 C2`
- P0=0xF9 (`1111_1001`): W=1 leaked to bit[0] → m0=1 → mm_eff=`001`=MAP1 (wrong, should be MAP2)
  AND reserved bit[3]=1 is set (via ERR-001a mm-shift) AND correct mm bits[2:0] are all zero
- P1=0xF5: W correctly at bit[7]=1 by coincidence (the `1 << 7` must-1 constant happens to
  equal the needed W=1 value), but this is accidental — for W=0 instructions P1[7] reads 1
  (wrong) via the same constant

The f64 buggy output has mm_eff=001 (MAP1 / `0F` legacy escape), which for opcode 0xA8 maps to
the `TEST r/m64, r64` group — a completely different instruction class. Any CPU executing this
sequence will either fault (SIGILL) or perform an unrelated operation.

### Required guard for M1 emitter

The M1 backend MUST add an explicit runtime assertion at emit time before accepting any EVEX
encoding function as correct. Minimum required check for MAP2 instructions (VFMADD213PS/PD,
VFMADD231PS/PD, and all 0F38-map AVX-512 opcodes):

```
fn emit_evex_guard(bytes: [u8; 6], expected_map: i32):
    byte1 = bytes[1]
    actual_mm = byte1 & 0x07        # bits[2:0] per Intel SDM §2.6.1
    reserved  = (byte1 >> 3) & 0x01 # bit[3] must be 0
    assert(actual_mm == expected_map,
        "EVEX emit: opcode-map bits wrong: got {actual_mm}, expected {expected_map}")
    assert(reserved == 0,
        "EVEX emit: reserved bit[3] of Byte1 is set — mm shift bug present")
```

For VFMADD213PS: `emit_evex_guard(bytes, 0b010)` (MAP2).
For VFMADD213PD: `emit_evex_guard(bytes, 0b010)` plus `assert((bytes[2] >> 7) & 1 == 1)` (W=1
at Byte2 bit[7]).

This guard will catch both ERR-001a and ERR-001b if the corrected encoder pseudocode is
transcribed incorrectly during M1 implementation.

### Test impact

The following Wave-F golden fixtures are blocked by ERR-001a/ERR-001b until the M1 emitter
uses the corrected encoder:

- **C3b §10.3 Fixture A-1**: `VFMADD213PS zmm0{k1}{z}, zmm1, zmm2 → 62 F2 75 C9 A8 C2`
  — cannot be stamped CANONICAL for production until M1 emits the correct bytes.

- **Any future Fixture A-2 / SAXPY-f64 golden** involving `VFMADD213PD` — the buggy encoder
  produces MAP1 corruption (`62 F9 F5 C9 A8 C2`) which will SIGILL on real hardware.

- **All other AVX-512 3-op ZMM goldens** derived from `evex_encode_3op_zmm` are suspect until
  individually re-verified against the corrected encoder.

Wave-F tests that use RVV (Fixtures R-1, R-2, R-4 in C3b §10.5) are unaffected; those
encoders are independent of `evex_encode_3op_zmm`.

---

## ERR-002 — N-3 BSL fixture in part2 §10.1 had wrong Rm encoding

**Corrected 2026-05-02.**

### Errata index row

| ID | Source doc + section | Severity | Status | Affected goldens |
|---|---|---|---|---|
| ERR-002 | `simd_backend_strict_emit_detail_part2.md` §10.1 Fixture N-3 | HIGH (wrong BSL bytes) | RESOLVED | N-3 BSL bytes in C3b §10.1 |

### Symptom

The original Fixture N-3 document entry for `BSL v2.16b, v1.16b, v3.16b` listed bytes
`0x62 0x1C 0x33 0x6E`. H2 NEON pilot reported Rm decoded to 19, not 3.

### Root cause (with field citations)

ARMv8 ARM §C7.2.22 BSL, 16B form (`Q=1`) bit-pattern:
```
0|Q|1|01110|0|11|Rm[4:0]|000111|Rn[4:0]|Rd[4:0]
```

For `BSL v2.16b, v1.16b, v3.16b` (Rd=2, Rn=1, Rm=3):
- `bits[20:16]` = Rm = 3 = `00011` → byte2 must have bits[4:0]=`00011`
- `bits[22:21]` = `size` = `11` (BSL group marker) → byte2 bits[6:5] = `11`
- Combined byte2 = `0110_0011` = `0x63`

Original byte2 was `0x33` = `0011_0011`, which decodes to: `size[1:0]=01`, Rm=`10011`=19.
Both the `size` field (bits[22:21]) and Rm (bits[20:16]) were wrong.
Full original word `0x6E331C62` decodes: Rm=19, Rn=3, Rd=2 — Rm and Rn both incorrect.

### Worked example: bad output vs corrected output

```
BAD   (original doc): BSL v2.16b, v1.16b, v3.16b → 0x62 0x1C 0x33 0x6E  (word 0x6E331C62)
                       Rm decoded=19, Rn decoded=3, Rd decoded=2 — two field errors

GOOD  (corrected):    BSL v2.16b, v1.16b, v3.16b → 0x22 0x1C 0x63 0x6E  (word 0x6E631C22)
                       Rm=3, Rn=1, Rd=2 — all fields correct per ARMv8 ARM §C7.2.22

Base opcode check (Rd=Rn=Rm=0): 0x00 0x1C 0x60 0x6E (word 0x6E601C00)
  byte2=0x60 = 0110_0000: size=11 (bits[22:21]), Rm=0 (bits[20:16]) ✓
```

### Test impact

`test/unit/compiler/backend/neon_emit_spec.spl` BSL goldens were derived from bit-field
analysis independently (not from the doc fixture) and were already correct. The UNVERIFIED
comment tags on those tests have been removed — they are now VERIFIED via §C7.2.22 derivation.

---

## Placeholder for future errata

Future bugs discovered in C3a/C3b should be added here with IDs ERR-003, ERR-004, etc.,
following the same structure: errata index row, symptom, root cause (with line citations),
worked example showing the bad output, corrected output, and test impact.

Candidate items not yet confirmed:
- C3a §4 (SVE2 encoder): V-08 status remains FAILED per D1 — primary ARM spec inaccessible;
  sve2 byte claims carry [UNVERIFIED] tag; errata pending ARM ISA XML resolution.
- C3b §10.4 Fixture N-3 (NEON FCMGT): V-25 status FAILED per D1 — operand-order question
  unresolved; potential ERR-003 if ARM spec confirms operand reversal is wrong.

---

## Wave I5 audit log — 2026-05-02

**Scope:** All emit helper bodies in `x86_64_avx512.spl` and `arm_neon.spl` cross-referenced
against part1/part2 doc fixtures and inline §-citations.

**Opcodes audited (10 helpers):**

| Helper | File | Doc fixture | Result |
|--------|------|-------------|--------|
| `emit_avx512_kandb_kreg_3op` | x86_64_avx512.spl | No standalone fixture in part1/part2 | AUDITED: agree (emitter `C5 ED 41 CB` matches inline comment + llvm-mc) |
| `emit_avx512_korb_kreg_3op` | x86_64_avx512.spl | No standalone fixture | AUDITED: agree (`C5 ED 45 CB`) |
| `emit_avx512_kxorb_kreg_3op` | x86_64_avx512.spl | No standalone fixture | AUDITED: agree (`C5 ED 47 CB`) |
| `emit_avx512_kandnb_kreg_3op` | x86_64_avx512.spl | No standalone fixture | AUDITED: agree (`C5 ED 42 CB`) |
| `emit_avx512_kmovw_gpr_to_k` | x86_64_avx512.spl | No standalone fixture | AUDITED: agree (`C5 F8 92 C8`) |
| `emit_avx512_vpcmpeqd_zmm_to_k` | x86_64_avx512.spl | No standalone fixture; uses `evex_encode_zmm_to_kreg_2op` | AUDITED: covered by ERR-001 family |
| `emit_neon_vaddq_f32` | arm_neon.spl | N/A (no doc fixture for FADD 3-same) | AUDITED: agree (docstring `0x00 0xD4 0x20 0x4E` ✓) |
| `emit_neon_vmulq_f32` | arm_neon.spl | N/A | AUDITED: agree (docstring `0x00 0xDC 0x20 0x6E` ✓) |
| `emit_neon_vfmaq_f32` | arm_neon.spl | Fixture N-1 is scalar-indexed (different instruction class) | AUDITED: agree (docstring `0x00 0xCC 0x20 0x4E`; N-1 uses 0F-class FMLA, not 4E-class) |
| `emit_neon_vbslq_u8` | arm_neon.spl | Fixture N-3 | AUDITED: mismatch already filed as ERR-002 by I3 |

**Additional fixture checks (no emitter counterpart):**

- Fixture N-2 (FADDP `0x6E20D400`): byte-field decode confirms Q=1, U=1, opcode=11010 — plausibly correct; UNVERIFIED tag appropriate.
- Fixtures A-1/A-2/A-3 (AVX-512 EVEX): all UNVERIFIED; structural decode consistent with Intel SDM EVEX layout; no new byte errors found.

**New errata filed: none.** The only confirmed byte mismatch in scope is ERR-002 (BSL N-3), already filed by I3.
