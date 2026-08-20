# engine2d SIMD row/span kernels are slower than scalar, and `fill_span` corrupts the fill colour

Status: PARTIALLY RESOLVED / OPEN (P3, downgraded from P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## 2026-08-20 — §1 RESOLVED (measured), §2 retraction confirmed a third time, §3 partly done

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, `59773320 2026-08-19
15:14:28`, md5 `a6dd60aa14b89f259a7cc8b67f374c25` (still the Rust seed). Same
harness, 7 fresh processes, 640-px span, 400 iters.

**§1 is fixed — no kernel is a pessimisation any more.** Two source-local edits
in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`:

- `simd_fill_row` (`:425`) — native branch REMOVED. A fill broadcasts a
  constant, so the native round trip (extern call + a fresh `count`-element
  malloc in C + `count` boxed stores + a `count`-element `write_span` back) is
  ~3x the memory traffic of the scalar store loop and can never win. This is not
  a re-run of §1's old global mitigation: `copy`/`blit` keep their native paths,
  which are real wins.
- `simd_blend_row` (`:452`) — now calls the in-place
  `rt_engine2d_simd_blend_span_u32` instead of `engine2d_simd_blend_row_u32`.
  Because the span kernel takes a src offset, `src` is read in place: one fewer
  Simple allocation and one fewer `write_span` here, and zero `malloc`s plus no
  unbox/rebox scratch round trip in C (the two mallocs §3 complains about).

| kernel | before (native) | after (native) | scalar |
|--------|-----------------|----------------|--------|
| fill   | 7 ms            | **0 ms**       | 0 ms   |
| copy   | 0 ms            | 0 ms           | 13 ms  |
| blend  | 30 ms           | **25 ms**      | 28 ms  |
| blit   | 0 ms            | 0 ms           | 13 ms  |

p50; max RSS 51.9 MB (was 52.1). Blend now BEATS scalar for the first time.

**Correctness.** `test/perf/graphics_2d/blend_parity_probe.spl` reports
`PARITY_DIFFS=0` on the new blend path. New pin:
`test/perf/graphics_2d/span_kernel_pixel_correctness_spec.spl` — 4/4 pass,
decoding every pixel by shift+mask (never by decimal, the mistake that created
§2). It is verified to DISCRIMINATE: injecting a one-pixel src-offset error into
the new blend call turns it red (3 passed / 1 failed).

**§2 retracted a third time, now on this lane's code.** The exact repro
(`rt_engine2d_simd_fill_span_u32(a, 2, 4, 0xFF112233)`) returns `a=255 r=17
g=34 b=51` = `0xFF112233` byte-exact at indices 2..5, 0/1/6/7 untouched. There
is no colour corruption and no boxing defect: `engine2d_box_pixel` is
`pixel << 3` / `>> 3` (`runtime_simd_dispatch.c:663/667`), a tag shift that
cannot alter a byte. §2 should be treated as closed, not as open work.

**§3 partly closed by the above** — the in-place blend span is now ADOPTED in
the Simple blend path, and the native `fill` regression is fixed. **Still
blocked:** `rt_engine2d_simd_blit_row_u32` does not exist, and adding it means
editing `src/runtime/runtime_simd_dispatch.c`, which cannot be exercised without
rebuilding and redeploying the shared `bin/release/x86_64-unknown-linux-gnu/simple`
— the same bootstrap-redeploy blocker §3 recorded on 2026-08-06. No C file was
touched in this pass. Note that `blit` already measures 0 ms via `write_span`,
so the missing kernel is not currently costing anything.

## Live re-run 2026-08-17 (measured, not inspected)

Binary: `readlink -f bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple`,
`stat -c '%s %y'` = `59537240 2026-08-17 12:58:51 +0000`, md5
`78ffcbcd3f4cfaa11e3d9c1db37bf0b2` (still the Rust seed — it prints the seed
banner). Same harness, same 11-fresh-process protocol, 640-px span, 400 iters:

```
sh test/perf/graphics_2d/run_span_bench.shs 11 native            # default (auto)
SIMPLE_2D_SIMD=off sh test/perf/graphics_2d/run_span_bench.shs 11 scalar
```

| kernel | native p50 | scalar p50 | native p99 | scalar p99 |
|--------|-----------|-----------|-----------|-----------|
| fill   | **7 ms**  | **0 ms**  | 11 ms     | 3 ms      |
| copy   | **0 ms**  | 13 ms     | 0 ms      | 17 ms     |
| blend  | 40 ms     | **28 ms** | 92 ms     | 40 ms     |
| blit   | **0 ms**  | 12 ms     | 1 ms      | 18 ms     |
max RSS: 43.8 MB native vs 48.3 MB scalar.

**What changed since 2026-08-06:** `copy` and `blit` are no longer parity — they
are now dramatically FASTER native (0 ms vs 12-13 ms), and native RSS is now the
lower of the two. This is the effect of the `write_span` bulk write-back channel
(see the 2026-08-15 comment block at `simd_kernels.spl:409`), which removed the
interpreted per-pixel scatter that §1 blamed.

**What is still true:** `fill` and `blend` remain pessimisations native
(7 vs 0 ms, 40 vs 28 ms p50; blend's p99 is 2.3x worse), so §1's core claim
survives for those two kernels only.

**Correction to §1's "Action taken":** that mitigation is NO LONGER in the
source. `native_pixel_rows_enabled()`
(`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:392-403`) now returns
`true` under `auto` whenever an ISA is detected — only an explicit
`SIMPLE_2D_SIMD=off` selects scalar. Confirmed live: the default run prints
`native_rows=true`, `SIMPLE_2D_SIMD=off` prints `native_rows=false`. So the
default lane today takes the slower `fill`/`blend` paths.

**§2 re-confirmed non-defect.** The exact repro was re-run
(`rt_engine2d_simd_fill_span_u32(a, 2, 4, 0xFF112233)`, decoded by shift+mask,
never by decimal): indices 2..5 = `a=255 r=17 g=34 b=51` = `0xFF112233`
byte-exact; 0,1,6,7 untouched. The retraction stands.

**§3 mostly closed.** `rt_engine2d_simd_blend_span_u32` (`:2048`) and
`rt_engine2d_simd_blend_const_span_u32` (`:2113`) now EXIST in
`src/runtime/runtime_simd_dispatch.c` and are declared in
`simd_native_rows.spl:7,8`. Only `rt_engine2d_simd_blit_row_u32` is still
absent (0 grep hits). Remaining work is therefore: adopt the in-place blend
span in the Simple blend path, fix the native `fill` regression, and add
`blit_row` — not "there is no in-place blend kernel at any layer".

**Filed:** 2026-08-06 · **Severity:** high (perf regression by construction + wrong pixels)
**Workstream:** WS-D (2D perf), findings D-F2 / D-F3 / D-F9
**Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `ed53cc5f255e269ca27c4cd83b17aef9`, 57 MB — **this is a Rust seed build**
(it emits `src/compiler_rust/driver/src/seed_warning.rs`'s banner). Engine is
therefore JIT-over-Cranelift with C-runtime externs, not self-hosted native.
Host: x86_64, AVX2 present.

## 1. The native row path is a measured pessimisation

Harness: `test/perf/graphics_2d/bench_span_kernels.spl`, driven by
`test/perf/graphics_2d/run_span_bench.shs` — 11 fresh processes per mode
(`native_pixel_rows_enabled()` memoizes, so an in-process env matrix would
measure the first value N times), run 1 discarded, 400 iterations of a 640-pixel
span per kernel.

| kernel | native rows p50 | scalar p50 | native p99 | scalar p99 |
|--------|-----------------|-----------|-----------|-----------|
| fill   | 8 ms            | **0 ms**  | 8 ms      | 1 ms      |
| copy   | 13 ms           | 13 ms     | 15 ms     | 21 ms     |
| blend  | 64 ms           | **27 ms** | 69 ms     | 29 ms     |
| blit   | 13 ms           | 13 ms     | 15 ms     | 22 ms     |

max RSS: 42.7 MB native rows vs **34.8 MB** scalar.

Cause (`simd_kernels.spl:simd_fill_row`, `:simd_blend_row`): each call allocates
a fresh row array, runs an interpreted per-pixel gather, crosses the FFI
boundary, then runs an interpreted per-pixel scatter. Three O(n) passes replace
one. The C kernel itself is fine — the marshalling around it is the cost.

**Action taken:** `native_pixel_rows_enabled()` now returns `false` unless
`SIMPLE_2D_SIMD` explicitly names an ISA (`sse2|avx2|neon|rvv|on`). `auto`
(the default) and `off` both select scalar. The native bodies stay reachable so
the kernels remain testable.

## 2. `rt_engine2d_simd_fill_span_u32` corrupts the fill colour

> **RETRACTED 2026-08-07 — false positive.** The "expected"/"observed" decimal
> values below are both mis-converted from hex: `0xFF112233` = `4279312947`
> (not `4279173683`), and `4279312947` is therefore the **correct** decimal
> value of the input colour, not a corrupted output. A live re-run of this
> exact repro against current `main` produced byte-exact output
> (`255.17.34.51` = `0xFF.0x11.0x22.0x33`, verified via shift+mask, not
> decimal comparison). There is no colour-boxing defect in
> `engine2d_box_pixel`/`engine2d_unbox_pixel` and no fix is needed. Full
> evidence: `doc/03_plan/ui/perf/engine2d_simd_fill_span_colour_boxing_fix_plan_2026-08-07.md`.
> §1 (perf) and §3 (missing blend span kernel) are unaffected by this
> retraction.

The in-place span externs (`simd_native_rows.spl:5,6`) look like the right fix
for §1 — `fill_span`/`copy_span` mutate `dst` and return it, no marshalling. But:

```simple
var a: [u32] = [0; 8]
val out = rt_engine2d_simd_fill_span_u32(a, 2, 4, 0xFF112233 as u32)
```

Span placement is correct (indices 2..5). The **value** is not:

| | |
|---|---|
| expected | `0xFF112233` = 4279173683 |
| observed | `0xFF132233` = 4279312947 |

The green byte `0x11` comes back as `0x13`. `rt_engine2d_simd_copy_span_u32`
under the same probe is **correct**, so this is specific to the colour argument's
boxing across the `u32` extern parameter, not to the span logic
(cf. D-F9: pixel words are boxed `int64_t` via `engine2d_box_pixel` /
`engine2d_unbox_pixel`, `runtime_simd_dispatch.c:663/:667`).

It is also *slower* than the marshalling path it would replace: 13 ms vs 8 ms
vs <1 ms scalar, same harness.

So `fill_span` cannot be adopted until the colour marshalling is fixed. Wired it
up, measured it, reverted it — recorded here rather than merged.

## 3. Still missing: an in-place blend span kernel

`fill_span`/`copy_span` have in-place externs; **blend does not**. Even the
native `rt_engine2d_simd_blend_row_u32` (`runtime_simd_dispatch.c:1454`)
`malloc`s two scratch buffers and unboxes/reboxes every pixel (`:1467-1476`),
and its malloc-failure fallback is also per-pixel unbox/blend/box. There is no
allocation-free blend path at any layer today.

The C work (`rt_engine2d_simd_blend_span_u32` /
`rt_engine2d_simd_blend_const_span_u32` / `rt_engine2d_simd_blit_row_u32`,
WS-D D2.1/D2.2) is **not done in this pass**: exercising a new
`runtime_simd_dispatch.c` symbol requires rebuilding and redeploying
`bin/release/x86_64-unknown-linux-gnu/simple`, the binary other live sessions
resolve. Landing an unverifiable kernel there was judged a worse trade than
filing it. Blocked on: a way to build and run the C runtime without swapping the
shared deployed binary. Fix §2 first — the same boxing discipline applies.

## 4. Not evidence of anything on SimpleOS/QEMU

The C SSE2/AVX2 blend kernel is reachable and **numerically correct** under JIT
on this x86_64 host (`test/perf/graphics_2d/blend_kernel_probe.spl`: the extern
matched the reference formula on all probed cases). That says nothing about
SimpleOS or QEMU — no SimpleOS SIMD measurement was taken and none should be
inferred from this host result.

## Related

- `doc/08_tracking/bug/any_receiver_element_read_shift_and_tag_2026-08-06.md` —
  the scalar blend fallback these numbers now route to was itself producing
  wrong pixels until 2026-08-06; the "scalar" column above is post-fix.
- `doc/03_plan/os/simpleos/screens/ws_d_2d_perf_detail.md` — D-F2, D-F3, D-F9.
- D-F8 (facade ownership) is **already resolved at HEAD**: the
  `nogc_async_mut/gpu/engine2d/simd_{kernels,provider}.spl` files are 21- and
  9-line re-export facades over `nogc_sync_mut`, and exactly one
  `fn simd_blend_row` exists in `src/lib`. There is no duplicate implementation.
