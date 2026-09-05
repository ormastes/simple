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

## Variable-alpha opaque-destination optimization

The variable-source production span now preserves memmove-style overlap order
while handling transparent and opaque sources directly. When the retained
destination is opaque, output alpha and the divisor are fixed at 255; only
translucent destination pixels use the fully general source-over formula. This
removes two 256-pixel gather/scatter scratch rows from the common path.

Native full-frame variable blend improved from p50 542,337,679 ns to
160,778,922 ns (3.37×), with p95 172,583,479 ns. Fifteen-sample retained runs
measured p95 8,112,508 ns at 5% damage (PASS) and 12,828,783 ns at 7.5%
(FAIL). After both blend optimizations, **5% is the measured conservative
all-operation isolated envelope** on this host. This remains below an
end-to-end guarantee because multiple operations and frame-management overhead
must share 12.5 ms. AArch64 and RVV QEMU correctness gates pass, including a
280-pixel overlapping same-array span crossing the former scratch boundary.

## AVX2 vector output follow-up

The x86-64 opaque-destination kernel previously vectorized channel
multiplication, then spilled all three channel accumulators to stack, performed
24 scalar divisions per eight pixels, rebuilt eight boxed values scalar, and
stored them individually. The follow-up keeps exact division by 255, channel
assembly, and Simple pixel boxing in AVX2 registers through the final stores.

On the same native 7680x4320, one-percent-damage, seven-sample harness, the
before/after p95 measurements were:

| Operation | Before ns | After ns |
|---|---:|---:|
| variable alpha blend | 1,146,163 | 667,181 |
| constant alpha blend | 1,155,741 | 493,558 |
| six-call frame | 3,272,168 | 2,051,119 |

Both runs produced checksum `2436809228175672195`; the after run recorded 35
native SIMD hits, and the native C kernel plus in-place span corpus passed.
Seven-sample p95 is directional host evidence rather than a broad statistical
claim. This remains an isolated retained-damage operation row: it does not prove
full-frame CPU 8K/80, end-to-end DrawIR/GUI/WM throughput, physical display
scanout, or ARM/RISC-V hardware performance.

## NEON variable-source vector output follow-up

The AArch64 opaque-destination variable-source kernel now likewise keeps exact
division by 255, channel assembly, and boxed-pixel stores in NEON registers.
The constant-source path retains its former scalar output tail because applying
the same rewrite there regressed its matched QEMU p95; this operation-specific
selection avoids accepting that tradeoff.

At 7680x4320 with one-percent damage and seven samples under static
`aarch64-linux-gnu-gcc` output on `qemu-aarch64 -cpu max`, p95 changed as
follows:

| Operation | Before ns | After ns |
|---|---:|---:|
| variable alpha blend | 5,823,379 | 4,136,169 |
| constant alpha blend | 3,138,710 | 3,071,448 |
| six-call frame | 11,712,694 | 9,718,280 |

The AArch64 NEON C kernel and in-place span corpus passed. Both benchmark runs
produced checksum `2436809228175672195`, and the final run recorded 42 native
SIMD hits. This demonstrates bit-exact cross-architecture execution and a QEMU
regression direction. Emulator timing is not physical ARM performance, bare
metal scanout, or end-to-end 8K/80 proof.

## 2026-08-13 host revalidation — frame-switch boundary

The native C harness was rerun on the x86-64 host with the current
`runtime_simd_dispatch.c` and seven samples.  At 7680x4320 with **1% active
damage** (331,776 pixels), the six-call retained operation frame recorded p95
**2,394,350 ns**, checksum `2436809228175672195`, and 35 native SIMD hits.  The
isolated active-damage primitive budget therefore passed.

The same harness at **100% active damage** recorded six-call p95
**379,656,624 ns** (checksum `6655426588272231299`), so the full-repaint budget
failed.  This is expected memory-bandwidth pressure from six 8-byte-per-pixel
buffer operations, not evidence that the retained route has regressed.

This is still operation-level native C evidence only. It does not prove
end-to-end DrawIR, GUI, WM, physical scanout, ARM/RISC-V hardware performance,
or dynamic 8K/80 application throughput.

## SSE2 fallback vectorization and forced-dispatch evidence

The x86-64 SSE2 fallback previously invoked a one-pixel helper for every pixel.
It now processes four opaque-destination pixels at a time using SSE2 byte
unpacking, 16-bit channel multiplication, exact division by 255, packed channel
assembly, and boxed 64-bit stores. Mixed-alpha destinations and scalar tails
retain the exact general oracle. A compile-time-only
`SIMPLE_RUNTIME_FORCE_NO_AVX2` switch makes this fallback directly measurable on
an AVX2 host without changing normal runtime dispatch.

On the native 7680x4320, one-percent-damage, seven-sample harness with forced
SSE2 dispatch, p95 changed as follows:

| Operation | Before ns | After ns |
|---|---:|---:|
| variable alpha blend | 4,642,000 | 929,329 |
| constant alpha blend | 4,652,659 | 734,316 |
| six-call frame | 10,089,472 | 2,944,076 |

The forced-SSE2 C kernel and in-place span corpus passed. Both benchmark runs
produced checksum `2436809228175672195`; the after run recorded 35 native SIMD
hits. This proves the production SSE2 fallback under forced dispatch and its
isolated retained-damage envelope, not full-frame or end-to-end 8K/80.

## 2026-08-13 refreshed one-percent host row

The current tree was measured again with
`ENGINE2D_SIMD_8K_ACTIVE_BASIS_POINTS=100 sh scripts/check/check-engine2d-simd-8k-ops.shs`.
At 7680x4320 with 331,776 active pixels, seven samples produced six-call p50
`1,424,553 ns`, p95 `1,710,737 ns`, checksum
`2436809228175672195`, and 35 native SIMD hits. Individual p95 values were
250,497 ns fill, 275,725 ns copy, 565,917 ns variable blend, and 500,824 ns
constant blend. The harness reported
`engine2d_8k_active_damage_primitive_budget_met=true` and
`engine2d_8k_full_dynamic_frame_80fps_proven=false`.

This refresh is an operation-level native C retained-damage row. It does not
establish a self-hosted Simple DrawIR/Web/GUI/WM frame, GPU presentation,
physical scanout, or a full dynamic 8K/80 result.

## 2026-08-13 current full-frame x86 revalidation

The current vector-blend runtime (including the AVX2/SSE2/NEON/RVV boxed-span
implementations) was measured again with the canonical native C harness at
100% active damage. Runtime source revision: `1da6889c5dd`; command:

```sh
BUILD_DIR=build/check/engine2d-simd-8k-ops-current-20260813 \
  sh scripts/check/check-engine2d-simd-8k-ops.shs
```

| Operation | p50 ns | p95 ns | 12.5 ms operation budget |
|---|---:|---:|---|
| fill | 25,659,712 | 26,195,297 | FAIL |
| copy | 22,081,525 | 22,222,845 | FAIL |
| variable alpha blend | 60,966,735 | 62,520,087 | FAIL |
| constant alpha blend | 49,290,170 | 52,176,664 | FAIL |
| six-call frame | 210,360,430 | 211,572,430 | FAIL |

The final checksum was `6655426588272231299`, native SIMD hits were `35`, and
maximum RSS was `519,680 KiB`. This is a substantial improvement over the
older scalar-heavy blend rows, but the canonical harness still emitted
`engine2d_8k_full_dynamic_frame_80fps_proven=false`. It is native C runtime
evidence, not a self-hosted Simple application or end-to-end display result.

## 2026-08-13 current QEMU ISA rows at one-percent damage

The current runtime was cross-compiled from the same source and run through the
canonical operation harness at 1% active damage (331,776 of 33,177,600 pixels,
seven samples). Both rows preserved checksum `2436809228175672195` and recorded
42 SIMD-hit receipts. These are target instruction/parity checks under QEMU;
their timings are not physical ARM/RISC-V or bare-metal results.

| Target / emulator | Fill p95 | Copy p95 | Blend p95 | Const blend p95 | Six-call p95 | Isolated primitive budget |
|---|---:|---:|---:|---:|---:|---|
| AArch64 NEON / `qemu-aarch64` | 0.641 ms | 0.785 ms | 3.885 ms | 2.999 ms | 9.327 ms | PASS |
| RV64GCV VLEN=128 / `qemu-riscv64` | 2.798 ms | 5.633 ms | 24.117 ms | 16.186 ms | 53.688 ms | FAIL |

Commands used `aarch64-linux-gnu-gcc -static -march=armv8-a+simd` and
`riscv64-linux-gnu-gcc -static -march=rv64gcv -mabi=lp64d`, with the RISC-V
runner fixed to `-cpu rv64,v=true,vlen=128,elen=64`. The ARM QEMU row fits this
narrow retained primitive mix; the RVV QEMU row does not. Neither result proves
an 8K/80 application, self-hosted Simple execution, display scanout, or
hardware performance.

## 2026-08-13 freestanding span ABI check

Current source revision `4fd694ea7c5` passed:

```sh
sh scripts/check/check-simpleos-baremetal-engine2d-spans.shs
```

The check compiles the Engine2D span contract with the SimpleOS x86_64 boot
stubs at `-O3`, links only the required freestanding symbols, and executes its
bit-exact fill/copy/blend assertions on the host. It verifies that the span ABI
remains linkable for the baremetal target after the retained-damage work.

It is intentionally **not** a guest boot, QEMU framebuffer, physical-board,
or throughput result. The existing SimpleOS desktop QEMU gate remains unable to
establish an 8K/80 baremetal claim; no such claim is made here.

## 2026-08-13 refreshed native retained-operation receipt

Current source revision `80c9d2c3250` was measured with the hardened
single-owner harness:

```sh
BUILD_DIR=build/check/engine2d-simd-8k-ops-retained-current-20260813 \
  ENGINE2D_SIMD_8K_ACTIVE_BASIS_POINTS=100 \
  sh scripts/check/check-engine2d-simd-8k-ops.shs
```

At 7680×4320 with 331,776 active pixels (1%), seven samples produced these
native x86 receipts:

| Operation | p50 ns | p95 ns |
|---|---:|---:|
| fill | 44,065 | 221,174 |
| copy | 84,723 | 270,970 |
| variable alpha blend | 488,767 | 536,199 |
| constant alpha blend | 425,235 | 470,432 |
| six-call retained mix | 1,169,542 | 1,505,216 |

The checksum was `2436809228175672195`, the native SIMD receipt count was
`35`, and maximum RSS was `519,680 KiB`. Every isolated operation satisfied
the 12.5 ms primitive budget. The receipt still emitted
`engine2d_8k_full_dynamic_frame_80fps_proven=false`: it excludes retained
DrawIR traversal, WM copying/frame switching, scheduling, and scanout, so it
must not be promoted to an application 8K/80 claim.

## 2026-08-13 operation revalidation — native and QEMU retained damage

Revision `7af3af8d516` was measured through the canonical native C span
harness at 7680×4320 with 1% active damage (331,776 pixels), seven samples,
and checksum `2436809228175672195`. Each row recorded nonzero SIMD hits.

| Lane | Execution | Fill p95 | Copy p95 | Blend p95 | Const blend p95 | Six-call p95 | Isolated 12.5 ms budget |
|---|---|---:|---:|---:|---:|---:|---|
| x86-64 | native C | 0.242 ms | 0.332 ms | 0.809 ms | 0.682 ms | 2.169 ms | PASS |
| AArch64 NEON | QEMU user emulation | 0.695 ms | 0.810 ms | 3.961 ms | 4.495 ms | 10.947 ms | PASS |
| RV64GCV VLEN=128 | QEMU user emulation | 4.603 ms | 8.633 ms | 32.778 ms | 27.075 ms | 80.038 ms | FAIL |

Commands were the canonical `check-engine2d-simd-8k-ops.shs`, setting
`ENGINE2D_SIMD_8K_ACTIVE_BASIS_POINTS=100`; cross rows used
`aarch64-linux-gnu-gcc` or `riscv64-linux-gnu-gcc -march=rv64gcv -mabi=lp64d`
with the matching QEMU user runner. The same source also passed
`check-simpleos-baremetal-engine2d-spans.shs` and C target execution on x86,
QEMU AArch64, and QEMU RISC-V.

The AArch64 and RVV timings are emulator-specific correctness/dispatch
evidence, not physical-board or bare-metal performance. The RVV row fails the
retained primitive budget under QEMU; it must not be promoted to an ARM/RISC-V
8K/80 application claim. All rows remain operation-level evidence: they
exclude self-hosted Simple execution, Web/GUI/WM traversal, presentation, and
display scanout; full dynamic 8K/80 remains unproven.
