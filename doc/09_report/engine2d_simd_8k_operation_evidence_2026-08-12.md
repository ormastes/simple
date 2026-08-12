# Engine2D SIMD 8K Operation Evidence — 2026-08-12

Status: **FAIL for full-frame CPU 8K/80; PASS for reproducible operation evidence**

Revision tested: `d158853ff225408a722e28420b6df20250d10299`

The production span ABI was measured over 7680×4320 (33,177,600 pixels), using
boxed 64-bit Simple array storage (265,420,800 bytes per buffer). The frame
budget is 12,500,000 ns. Every lane produced checksum
`6655426588272231299` and nonzero native-SIMD hit receipts.

| Lane | Execution | Operation | p50 ns | p95 ns | Single-op budget |
|---|---|---:|---:|---:|---:|
| x86-64 AVX2 | native, Threadripper 1950X | fill | 25,343,333 | 28,563,493 | FAIL |
| x86-64 AVX2 | native | copy | 22,458,021 | 23,974,873 | FAIL |
| x86-64 AVX2 | native | variable alpha blend | 542,337,679 | 576,212,485 | FAIL |
| x86-64 AVX2 | native | constant alpha blend | 519,693,902 | 539,397,647 | FAIL |
| AArch64 NEON | QEMU user emulation | fill | 55,634,007 | 58,140,076 | not hardware proof |
| AArch64 NEON | QEMU user emulation | copy | 71,030,353 | 72,787,645 | not hardware proof |
| AArch64 NEON | QEMU user emulation | variable alpha blend | 2,040,145,280 | 2,040,921,783 | not hardware proof |
| AArch64 NEON | QEMU user emulation | constant alpha blend | 1,911,248,839 | 1,939,075,948 | not hardware proof |
| RV64GCV, VLEN=256 | QEMU user emulation | fill | 385,595,718 | 386,812,192 | not hardware proof |
| RV64GCV, VLEN=256 | QEMU user emulation | copy | 679,671,547 | 680,822,550 | not hardware proof |
| RV64GCV, VLEN=256 | QEMU user emulation | variable alpha blend | 3,903,884,301 | 3,908,718,846 | not hardware proof |
| RV64GCV, VLEN=256 | QEMU user emulation | constant alpha blend | 3,860,003,025 | 3,860,234,271 | not hardware proof |

Native x86 max RSS was 519,680 KiB. AArch64 and RVV QEMU max RSS were
527,360 KiB and 527,284 KiB respectively. QEMU results prove cross-architecture
execution and exact output, not physical ARM/RISC-V throughput.

Conclusion: full-frame CPU repaint cannot achieve 8K/80 on the measured host,
even for fill or copy alone. CPU eligibility therefore depends on retained
frame switching, exact damage plans, and sufficiently small dirty regions.
This operation benchmark does not include scheduling, DrawIR traversal,
presentation, readback, or display scanout and deliberately emits
`engine2d_8k_full_dynamic_frame_80fps_proven=false`.

Reproduce with `scripts/check/check-engine2d-simd-8k-ops.shs`. Cross lanes set
`CC`, `ENGINE2D_SIMD_8K_CFLAGS`, `ENGINE2D_SIMD_8K_RUNNER`, and
`ENGINE2D_SIMD_8K_MODE`; raw receipts are written to the selected build
directory as `receipt.env`.

## Native x86 retained-damage envelope

The same production ABI can restrict work with
`ENGINE2D_SIMD_8K_ACTIVE_BASIS_POINTS` (100 = 1%). This models a contiguous
horizontal-band damage payload while retaining the full 8K allocation. A
15-sample native run at 1% (331,776 pixels) measured:

| Operation | p50 ns | p95 ns | Isolated 12.5 ms budget |
|---|---:|---:|---:|
| fill | 219,010 | 287,921 | PASS |
| copy | 287,761 | 313,320 | PASS |
| variable alpha blend | 5,173,988 | 5,440,439 | PASS |
| constant alpha blend | 5,190,500 | 5,608,681 | PASS |

A coarse sweep found fill and copy still individually below budget at 42.5%,
while blend became unstable around 2%–2.5% (7-sample p95 ranged from 12.1 ms to
17.4 ms). Therefore **1% is the measured conservative all-operation envelope**
on this host. It is not a whole-frame guarantee: DrawIR traversal, damage-plan
construction, multiple operations, scheduling, presentation, and scanout must
share the remaining budget. Arbitrary disjoint rectangles may have different
cache behavior and require separate evidence.

## Constant-alpha direct-buffer optimization

The original constant-alpha production span gathered and unboxed a 256-pixel
destination row, materialized a second constant-source row, ran the general
variable-alpha kernel, then boxed and scattered the result. Replacing that
path with direct boxed-buffer traversal, precomputed source terms, an exact
opaque-destination denominator, and the general formula only for translucent
destinations reduced native full-frame p50 from 519,693,902 ns to 102,879,542
ns (5.05×). Full-frame p95 remains 105,194,024 ns and therefore still fails
8K/80.

Fifteen-sample retained-damage receipts measured constant-alpha p95 of
5,359,340 ns at 5% damage and 9,632,421 ns at 7.5% damage, both individually
within budget. At 10% the p95 was 13,812,478 ns and failed. The measured
conservative isolated envelope for this operation is therefore 7.5% on the
host. ARM NEON and RVV QEMU correctness gates pass for opaque, translucent,
and transparent destinations; those emulated runs remain correctness evidence,
not physical throughput evidence. This direct fixed-denominator path is not
yet credited with an operation-local SIMD hit, so explicit vector attribution
remains open even though surrounding fill and variable-blend calls make the
aggregate benchmark hit counter nonzero.
