# Engine2D SIMD span cross-architecture evidence — 2026-08-11

## Scope

Production `src/runtime/runtime_simd_dispatch.c` was compiled with the existing
7680-pixel operation harness
`test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c`.
Each row uses 500 samples and checks fill/copy/mixed-alpha parity, opaque output,
nonzero scalar checksum, and a native SIMD hit counter. No Simple compiler or
provider-label-only result is used.

## Results

| Target | Execution | Operation | p50 ns/row | p95 ns/row | scalar p50 ns | speedup | 8K-row p95 extrapolation |
|---|---|---:|---:|---:|---:|---:|---:|
| x86-64 `-march=native` | host | opaque image blend | 2,375 | 2,786 | 16,672 | 7.019x | 12.036 ms |
| x86-64 `-march=native` | host | opaque constant blend | 1,272 | 1,393 | 10,420 | 8.191x | 6.018 ms |
| x86-64 `-march=native` | host | fill | 1,312 | 1,613 | 1,132 | 0.862x | 6.968 ms |
| x86-64 `-march=native` | host | copy | 1,433 | 1,743 | 2,154 | 1.503x | 7.530 ms |
| x86-64 `-march=native` | host | mixed-alpha blend | 107,305 | 113,718 | 107,095 | 0.998x | 491.262 ms |
| AArch64 `armv8-a+simd` | QEMU user | opaque image blend | 96,223 | 109,118 | 213,939 | 2.223x | 471.390 ms |
| AArch64 `armv8-a+simd` | QEMU user | opaque constant blend | 10,771 | 11,833 | 150,157 | 13.940x | 51.119 ms |
| AArch64 `armv8-a+simd` | QEMU user | fill | 10,841 | 14,858 | 10,671 | 0.984x | 64.187 ms |
| AArch64 `armv8-a+simd` | QEMU user | copy | 14,899 | 21,481 | 14,007 | 0.940x | 92.798 ms |
| AArch64 `armv8-a+simd` | QEMU user | mixed-alpha blend | 131,341 | 149,085 | 259,446 | 1.975x | 644.047 ms |
| RV64GCV, VLEN 128 | QEMU user | opaque image blend | 34,266 | 39,685 | 221,213 | 6.455x | 171.439 ms |
| RV64GCV, VLEN 128 | QEMU user | opaque constant blend | 132,453 | 139,486 | 197,557 | 1.491x | 602.580 ms |
| RV64GCV, VLEN 128 | QEMU user | fill | 174,123 | 193,169 | 17,062 | 0.097x | 834.490 ms |
| RV64GCV, VLEN 128 | QEMU user | copy | 254,666 | 261,549 | 19,297 | 0.075x | 1,129.892 ms |
| RV64GCV, VLEN 128 | QEMU user | mixed-alpha blend | 153,713 | 160,386 | 338,797 | 2.204x | 692.868 ms |

All runs reported `mismatches=0`. Native hit counts were x86-64 1,500,
AArch64 2,000, and RV64GCV 1,500.

## Verdict

This does **not** prove full-frame 8K/80 rendering. The extrapolation multiplies
one 7680-pixel row p95 by 4320 and excludes command generation, clipping,
dispatch, scheduling, presentation, and readback. Only x86 opaque/constant/fill/
copy kernels fit the isolated 12.5 ms row-work budget; x86 mixed alpha does not.
QEMU rows prove cross-architecture execution and correctness, not physical Arm
or RISC-V performance.

The immediate optimization priorities are mixed-alpha vectorization on x86,
and dispatch/fill/copy repair on RVV. Frame switching/damage remains required to
avoid full-frame work for realistic mixed-alpha scenes.

### Allocation-free production backend wiring rerun

The software backend now calls the in-place image and constant blend span ABIs
directly, without allocating destination/source rows and gathering/scattering
each scanline. The image path is enabled by the same honest native-row check on
x86-64, AArch64, and RV64 rather than an x86-only name check. A source contract
passes 2/2 and the runtime C span/kernel gate passes bit-exactness.

The 7,680-wide host rerun (`-O3 -march=native`, 500 samples) reported opaque
image p50/p95 4,709/8,186 ns (3.761x scalar), opaque constant 2,335/2,905 ns
(7.393x), and mixed-alpha 120,410/262,082 ns (0.947x). It reported 1,500 SIMD
hits and zero mismatches. This is current isolated kernel evidence; the
self-hosted backend parity spec presently exits after setup without a verdict,
so no before/after backend allocation timing is claimed. Mixed alpha remains a
measured regression and cannot qualify an 8K/80 full repaint.

## Direct 8K rectangle blit and overlapping scroll

The production copy primitive was additionally exercised by
`engine2d_simd_rect_scroll_8k_bench.c` using real 7680×4320 boxed-pixel buffers,
20 samples, full-frame row blit, and one-row overlapping downward scroll.

| Target | Execution | Operation | p50 ms | p95 ms | scalar/libc p50 ms | Native hits | Parity |
|---|---|---:|---:|---:|---:|---:|---:|
| x86-64 `-march=native` | host | full blit | 36.146 | 165.230 | 23.953 | 0 | exact |
| x86-64 `-march=native` | host | scroll | 29.060 | 30.646 | 29.011 | 0 | exact |
| AArch64 `armv8-a+simd` | QEMU user | full blit | 78.210 | 234.646 | 51.173 | 172,780 total | exact |
| AArch64 `armv8-a+simd` | QEMU user | scroll | 71.969 | 73.864 | 37.933 | 172,780 total | exact |
| RV64GCV, VLEN 128 | QEMU user | full blit | 974.668 | 1,178.975 | 52.503 | 172,780 total | exact |
| RV64GCV, VLEN 128 | QEMU user | scroll | 968.719 | 1,011.226 | 45.994 | 172,780 total | exact |

The x86 production copy path is explicitly `memmove`; it emits no native SIMD
receipt, so the harness correctly fails x86 SIMD admission despite parity. Arm
and RVV execute explicit vector loops, but QEMU timing is not physical-hardware
performance. Every measured p95 exceeds 12.5 ms. Host x86 peak RSS was 778,752
KiB because three boxed 8K buffers were held for parity.

These direct results prove that full-frame copy/scroll cannot currently meet
8K/80. Damage-limited frame switching is required, and RVV copy dispatch needs
repair before it should be preferred over libc/scalar copying.

## Bare-runtime static prerequisite update

`check-simpleos-qemu-engine2d-simd-kernels.shs` now passes real object
disassembly for ARM64 `dup`/`st1`, x86-64 `pshufd`/`movdqu`, and RV64 RVV
`vsetvli`/`vmv.v.x`/`vse32.v`. Its formerly over-escaped ARM64 `st1` predicate
is repaired. RV64 now uses runtime VL rather than assuming QEMU's VLEN. All
three objects export enabled/hit/chunk/tail/scalar-parity receipt symbols.

This is static prerequisite evidence only. No architecture receives a bare
8K/80 pass until a guest executes the kernel and supplies hit/chunk/parity,
QMP display capture, timing, fallback, and checksum receipts.

### RV64 production-kernel QEMU execution

`scripts/check/check-simpleos-rv64-gui-fill-qemu-user.shs` links the production
RV64 `baremetal_stubs.c` kernel into a freestanding Linux ELF and executes it
with QEMU `rv64`, RVV 1.0, VLEN 128. The probe passes exact clipped framebuffer
pixels, unchanged outside sentinels, enabled=true, hits=2, chunks>0, tail=0,
and scalar-parity=true.

This upgrades RV64 from object-only to executed production-kernel correctness.
It is still QEMU user mode, not a booted SimpleOS guest or display scanout, and
contains no presentation or 8K timing receipt. The `bare_riscv64` completion
matrix row therefore remains unqualified.

### Cross-ISA production bare-kernel execution matrix

`scripts/check/check-simpleos-gui-fill-qemu-user-matrix.shs` applies the same
8x4 framebuffer oracle to production boot runtimes: x86-64 SSE2 executes on the
host, ARM64 NEON executes under `qemu-aarch64`, and RV64 RVV executes under
`qemu-riscv64`. All three pass exact clipped pixels, outside sentinels, nonzero
hit/chunk receipts, expected tail accounting, and scalar parity.

This closes executed fill-kernel correctness across the requested ISAs. It
does not close bare-system rendering: these are user-mode harnesses linked from
production kernel objects, not booted SimpleOS display owners. Full guest/QMP
scanout and 8K timing receipts remain mandatory and absent.

The production fill owners now also track framebuffer height. The legacy
two-argument setter preserves its 768-line default, while the additive
`rt_gui_set_fb_size(address, width, height)` permits 4K/8K surfaces without an
ABI break. ARM64 no longer hard-clamps every fill to 768 rows, and x86-64/RV64
now clamp overflow-safe half-open rectangles to both dimensions. The live
oracle includes a bottom-right clipped draw plus a fully outside no-op and
verifies every surrounding sentinel. This is 8K-safe geometry evidence, not
an 8K allocation, scanout, or throughput measurement.

### 64×64 damage inside the same 8K buffers

The same harness measured a 64×64 rectangle for 200 frames without reducing the
7680×4320 allocation or parity oracle.

| Target | Execution | Operation | p50 µs | p95 µs | scalar/libc p50 µs | Admission note |
|---|---|---:|---:|---:|---:|---|
| x86-64 | host | damaged blit | 1.653 | 1.714 | 1.292 | budget pass; zero SIMD hits |
| x86-64 | host | damaged scroll | 1.362 | 1.422 | 0.982 | budget pass; zero SIMD hits |
| AArch64 NEON | QEMU user | damaged blit | 21.170 | 25.880 | 5.551 | budget pass; vector receipt |
| AArch64 NEON | QEMU user | damaged scroll | 20.629 | 21.110 | 5.190 | budget pass; vector receipt |
| RV64GCV | QEMU user | damaged blit | 127.944 | 137.933 | 4.188 | budget pass; vector receipt, severe regression |
| RV64GCV | QEMU user | damaged scroll | 125.610 | 141.641 | 9.468 | budget pass; vector receipt, severe regression |

All full-buffer parity checks pass. Arm/RVV total native hits increased to
198,180 after the damage samples. These rows prove only that sparse copy work
fits the isolated frame budget; they do not prove DrawIR/GUI/WM scheduling or
presentation. Since x86 lacks an ISA receipt and Arm/RVV lose to scalar/libc,
none is promoted as an optimized SIMD pass. They do demonstrate why exact
damage/frame switching is the viable route to 8K/80.

## Production software-backend allocation removal

`SoftwareBackend.draw_image_blend` now calls the in-place blend-span ABI on
each unclipped/mask-free row. It no longer allocates destination and source
rows, gathers both arrays, allocates a blended result, and scatters it back.
`sw_blend_const_raw_span` likewise calls the constant in-place ABI without its
two temporary rows. The production gate is no longer restricted to x86; the
same ABI dispatches on x86, AArch64, and RISC-V while preserving the scalar
backend fallback and dirty-span marking.

Backend SIMD parity passes 13/13, including varied alpha with negative-edge
clipping against the scalar backend and a source guard proving the production
path contains no temporary row arrays or legacy row-blend call. Whole-frame
damage parity passes 15/15,
including image blend, clipping, and masked slow paths. O3 optimizer analysis
passes for the backend and focused spec. A bounded `simple check` attempt was
terminated at 180 seconds without a source diagnostic while another compiler
closure was active, so no new backend p50/p95 is claimed from this source-only
wiring step. The isolated native span rows above remain the performance
evidence; full 8K repaint remains a measured failure.

## In-place ISA admission refresh

The canonical C gate had silently become unusable after an unrelated ML-KEM
block was inserted inside its broad source-extraction range. The extractor now
skips that marked block, and its standalone fixture defines the same AVX2
target annotation required by the production helpers. The gate passes again
on host x86-64, QEMU AArch64/NEON, and QEMU RV64GCV, including the in-place span
ABI and exact pixel oracle.

The in-place image span now classifies four boxed pixels at once on AVX2 and
NEON, copying fully opaque blocks directly and rejecting fully transparent
blocks without destination writes. ISA detection is hoisted once per span; the initial per-block CPUID
prototype measured a severe regression and was removed before admission.
Overlapping aliases retain sequential scalar behavior. Mixed blocks retain the
exact scalar blend math rather than claiming an ISA execution receipt.

Current 7,680-pixel, 500-frame rows (`-O3`; QEMU rows are emulation only):

| Target | Opaque image p50/p95 | Scalar p50 | Ratio | Opaque const p50 | Const ratio | Mixed p50 | Mixed scalar p50 | Parity |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| x86-64 host | 12,454/12,644 ns | 14,669 ns | 1.177x | 1,242 ns | 11.752x | 107,245 ns | 107,115 ns | exact |
| AArch64 QEMU | 59,083/69,152 ns | 223,457 ns | 3.782x | 10,901 ns | 13.779x | 155,848 ns | 302,558 ns | exact |
| RV64GCV QEMU | 30,879/36,470 ns | 222,064 ns | 7.191x* | 132,473 ns | 1.492x | 157,491 ns | 339,018 ns | exact |

All runs report zero mismatches. RVV image-vector promotion was explicitly
rejected after its VLEN=128 implementation measured 0.717x scalar; the final
7.191x image row is compiler-optimized four-pixel scalar organization and
carries no image SIMD receipt (hence `*`). RVV retains its faster opaque
constant vector path and receipt. The mixed rows likewise benefit from
four-pixel organization/compiler optimization but do not count as SIMD
admission unless an opaque block executes a real vector copy. Fill/copy regressions remain
visible and continue to require their runtime-local exact-and-faster gate.
These are row-kernel results, not full-frame or presentation proof.

## Production 8K damage-threshold hardening

`SoftwareBackend.damage_rects()` previously calculated both areas and
`bound_area * 100` as inferred signed i32 values. A 7680×4320 surface can
overflow that multiplication and choose the wrong retained/full-frame path.
The classifier now widens dimensions to i64 before multiplication and routes
through a pure geometry predicate. Its focused suite passes 17/17, including
64×64 sparse damage, exact 60% equality, and one-pixel-over-threshold cases at
8K. O3 optimizer analysis passes for source and spec.

The retained Web/DrawIR 8K runner also now propagates its declared timeout to
the repository CPU monitor instead of being killed at the monitor's unrelated
60-second default. A single current-source run still failed to reach rendering
within the corrected 180-second bound, so it produced no p50/p95 row and was
not retried. The existing native row/rect evidence remains valid, but a live
production-backend retained measurement is still blocked by compile latency.
