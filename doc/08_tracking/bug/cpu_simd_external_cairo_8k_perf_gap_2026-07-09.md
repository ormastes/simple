# CPU-SIMD External Cairo 8K Perf Gap

- **Date:** 2026-07-09
- **Status:** open
- **Severity:** high
- **Area:** GUI Web 2D, CPU-SIMD, performance

## Summary

The retained full-size 8K GUI benchmark shows Simple Web CPU-SIMD is still
slower than the available external CPU drawing-library baseline on this host.
This is an optimization blocker, not a correctness blocker.

## Evidence

`doc/09_report/gui_perf_benchmark_2026-07-08.md` records:

- Simple Web CPU-SIMD: `1282.166 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Node Canvas/Cairo: `80.201 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_target_met=no`.

Follow-up optimization on 2026-07-09 removed per-character glyph row-array
allocation from the CPU text path and re-ran the same retained 8K row:

- Simple Web CPU-SIMD: `938.678 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Improvement versus the recorded 2026-07-08 row: `26.8%`.
- Remaining gap versus Node Canvas/Cairo: `11.7x` slower.
- Evidence report: `doc/09_report/cpu_simd_text_glyph_inline_perf_2026-07-09.md`.
- Current owner blocker:
  `doc/08_tracking/bug/browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md`.

The current external CPU baseline refresh after the compare contract added
explicit quality and no-screen-reduction proof records:

- Simple Web CPU-SIMD: `767.872 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`, pixel proof
  `nonzero_pixels:33177600`.
- Simple Web scalar software: `799.203 ms` p50 with the same checksum.
- Node Canvas/Cairo: `73.892 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_dpi_source=default`.
- `gui_perf_cpu_base_compare_schedule_order=cpu_simd_first`.
- `gui_perf_cpu_base_compare_physical_pixels=7680x4320`.
- `gui_perf_cpu_base_compare_screen_size_reduced=false`.
- `gui_perf_cpu_base_compare_simple_checksum=sum32:135445232233405312`.
- `gui_perf_cpu_base_compare_simple_pixel_proof=nonzero_pixels:33177600`.
- `gui_perf_cpu_base_compare_runtime_compute_target=cpu_simd`.
- `gui_perf_cpu_base_compare_render_readback_scope=software-render-loop`.
- `gui_perf_cpu_base_compare_fallback_used=false`.
- `gui_perf_cpu_base_compare_target_met=no`.
- Current evidence report:
  `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`.
- Remaining gap versus Node Canvas/Cairo: `10.4x` slower.

`doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md` separately proves
the CPU-SIMD path beats the in-repo scalar software path for the focused 4K/8K
contract, so the remaining gap is external drawing-library parity.

## Expected

Either Simple Web CPU-SIMD reaches the external CPU drawing-library baseline for
the retained 8K scene, or the report keeps this blocker open with the measured
ratio and the bottleneck owner.

## 2026-07-10 stale deployment correction

The retained `767.872 ms` Simple row does not measure the optimized
`rt_array_repeat` implementation currently checked into the repository.
`bin/simple` resolves to the shared self-hosted release binary built on
2026-07-03. Disassembly of that binary's `rt_array_repeat` shows one
`rt_array_push` call per element; it does not contain the current first-store
plus doubling-`memcpy` implementation.

A focused full-8K repeat probe on that deployed binary measured `762414us` for
33,177,600 elements, matching the framebuffer trace and proving that the
retained result is dominated by the stale push loop. The recorded `10.4x`
Cairo ratio remains valid for the deployed 2026-07-03 binary, but it is not
valid evidence for the current source implementation.

An isolated pure-Simple bootstrap was attempted with the current source. Stage
2 failed at the known bootstrap LLVM/`llc` lane, and the seed-driven Cranelift
Stage 4 remained CPU-bound for 18 minutes without producing an executable. The
attempt was stopped at the existing bounded bootstrap ceiling. Three focused
AOT probe variants also failed in the current LLVM undefined-SSA/Cranelift type
lowering lane, so no substitute fresh executable was accepted.

Do not introduce packed framebuffer storage or another SIMD facade based on
the stale timing. First produce a fresh self-hosted CLI, confirm its
`rt_array_repeat` no longer contains the per-element push loop, then run the
retained 4K/8K and external Cairo comparisons once.

### Focused current-runtime result

After repairing Stage 2 LLVM emission, a standalone native probe compiled with
the fresh bootstrap runtime allocated and filled 33,177,600 `u32` elements,
validated the array length and final 32-bit color, and exited zero in `0.21 s`
wall time at `260096 KiB` max RSS. Its disassembly calls `memcpy` from
`rt_array_repeat`; it does not call `rt_array_push`.

This is a 3.6x improvement over the `0.762 s` stale push-loop probe and proves
the checked-in bulk-fill runtime is materially faster. It is not a replacement
for the retained full-render comparison: the fresh Stage 4 CLI currently fails
its standard smoke because its link accepted unresolved stubs, so no fresh
4K/8K or Cairo row is claimed yet.

### Strict linker follow-up

The reported 253-symbol strict exporter failure began as a pre-link aggregate:
the stub scanner examined undefined references in all object sections. Strict
mode now emits no stubs and lets the platform linker validate live sections
after GC. A focused Rust regression passes, and an independent Luna review
confirmed the ownership and minimal linker fix.

The in-process hosted-target build then proved that Cranelift emits one `.text`
section per Simple module, so importing `web_render_backend` kept its Chromium,
process/file, and every GPU backend reference linker-live even though this
exporter only requested the pure software layout method. The exporter now calls
`simple_web_layout_render_html_software_pixels` directly for all three accepted
software backend labels. That is behavior-identical to the removed
`web_render_backend("pure_simple", ...).render_html_software_pixels(...)` call
and removes the broad module closure without changing GPU production paths.
`cpu_simd_render_scale_contract_spec.spl` guards the absence of the generic
backend import and passes 9/9.

The full exporter still has no accepted fresh row. The debug bootstrap's
interpreted native-build worker timed out while loading/parsing the broad
closure at both 120 and 600 seconds, before producing a binary. This is the
existing `bootstrap_stage4_graph_load_timeout_2026-07-05` blocker; no reduced
viewport, cached replay, or stale binary result is substituted.

### In-process runtime closure follow-up

After narrowing the exporter, the strict in-process build reduced the failure
to live Simple-core ABI symbols and one native mangling collision. The
pure-Simple runtime now implements the required value untagging, string bytes,
UTF-8 character lookup, iterable identity, dynamic addition, and single-thread
bootstrap safepoint operations; a focused generated-archive C probe passes.
Engine2D color's private `_to_i32` helper was renamed `_u32_to_i32`, preventing
native suffix resolution from binding unrelated built-in `.to_i32()` calls to
that private function. The focused Engine2D color spec passes 7/7.

A strict Rust-runtime diagnostic binary then rendered full 3840x2160 and
7680x4320 frames in `46125us` and `149266us` respectively, with 329984 KiB max
RSS. Those timings are not accepted evidence: replacing `.to_i32()` with raw
casts for that build produced tagged-value checksum drift
(`17858061666742272` instead of the retained 8K checksum), so the workaround
was reverted. The corrected helper rename and Simple-core ABI must be rebuilt
and must reproduce the retained checksums before any current-source speed or
Cairo-ratio claim is made.

### Dynamic-repeat representation follow-up

The fresh MIR path passed raw scalar values to `rt_array_repeat`, whose first
argument is a boxed `RuntimeValue`. For a repeated `0xffffffffu32` framebuffer
initializer, typed reads therefore interpreted the raw bits as a tagged value
and returned `0x1fffffff`. MIR array-repeat lowering now boxes scalar elements
the same way ordinary array literals do. The focused MIR regression and the
dynamic `[u32; count]` compiler spec pass.

A strict pure-Simple-runtime binary built from commit `3f1e2e2ed0f` plus this
working change, using the retained
`build/check/cpu_simd_full_render_current_entry.spl` diagnostic, then produced
the correct full-width first
pixel (`indexed_first=raw_first=4294967295`) at both 3840x2160 and 7680x4320.
The measured render calls were `47856us` and `167412us`, with `326656 KiB` max
RSS, but both checksums equal an entirely white framebuffer:

- 4K: `35624176731648000` (`8294400 * 0xffffffff`)
- 8K: `142496706926592000` (`33177600 * 0xffffffff`)

These timings are rejected. They do not match the retained scene checksums
(`32105444634193792` at 4K and `135445232233405312` at 8K), so no fresh speed
or Cairo-ratio claim is made. The remaining correctness blocker is now after
framebuffer initialization: the strict Simple-core renderer does not commit
the scene's drawing writes.

### Strict Simple-core layout and SIMD-routing follow-up

The all-white result had two independent Simple-core ABI causes. Generated
index expressions pass tagged integer indices to `rt_index_get`/`set`, while
the Simple-core wrappers forwarded them as raw array offsets. The wrappers now
validate the integer tag and unbox the index. Simple-core also does not yet
provide the hosted Dict ABI used by CSS rule buckets, so missing dictionary
lookups now fall back to the bucket's compact key array; hosted runtimes retain
the O(1) dictionary path.

With those fixes, the exact canonical exporter fixture produced non-white,
bit-identical CPU-SIMD and scalar frames through the strict Simple-core binary:

- 4K: `sum32:35608179086024696`, CPU-SIMD `48318us`, scalar `46026us`.
- 8K: `sum32:142464551729943944`, CPU-SIMD `189180us`, scalar `174789us`.
- Both rows used full `3840x2160`/`7680x4320` physical sizes, default 300dpi,
  no size reduction, and no fallback.

Those checksums differ from the retained 2026-07-08 baseline because the
current renderer and fixture source have changed; no checksum constant is
updated until the retained contract is refreshed from an accepted binary.
The strict run also exposed that the exporter labeled the lane `cpu_simd` but
called only the scalar layout renderer (`simd_provider_hits=0`). A proposed
full-frame native copy route preserved exact transparency/opacity pixels in the
focused 6-case spec, but final review rejected it: it added redundant full-frame
copies and per-row allocations after scalar rasterization, so it measured data
movement rather than SIMD drawing. Generic RISC-V builds without
`__riscv_vector` could also have reported a logical provider hit while the C
runtime used its scalar fallback. The copy-only route was reverted.

The final strict 4K/8K rebuild was attempted three times after this routing
experiment. Each native closure build was externally terminated before
linking, including the narrow direct-row variant, so no post-routing full-size
timing or Cairo ratio is accepted. The bounded retry cap is reached; this
remains a build-environment/closure-load blocker rather than grounds for
replaying the pre-routing binary.

### Current-source 8K comparison

The 2026-07-10 profile runs full 7680x4320 at 300dpi with no size reduction.
The CPU-SIMD-labeled Simple path measures `2389.121ms`, uses `732768 KiB` max
RSS, and exactly matches the scalar checksum `sum32:17761116667698048`, but
reports `simd_provider_hits=0` and `native_simd_executed=false`. The scalar row
is `1461.001ms`; GTK3/Cairo reports `0.032ms` draw-only and 81408 KiB RSS.

This is retained failure evidence: the current lane is slower than scalar and
does not execute native SIMD. The Cairo row measures a narrower draw-only
operation, so its ratio is directional rather than semantic parity.

### In-place Engine2D span owner

The C runtime already provided mutable fill/copy span kernels, but the Simple
owner used return-row allocation plus element-by-element scatter. The software
backend now uses a cross-mode return-array fill bridge: native builds mutate
and return the same array, while the interpreter returns a replacement array
after running the Rust row kernel. This removes per-row allocation/scatter from
the native Engine2D fill owner without changing GPU backends or alpha math.

Focused evidence:

- Rebuilt-seed Engine2D backend spec: 14/14.
- Rebuilt-seed SIMD kernel spec: 20/20, including bounded-span adjacency.
- Native C span gate: pointer identity, exact `0xFF102030`, and a positive
  hardware-vector counter on x86_64.
- Runtime source compiles for x86_64, AArch64, generic RISC-V, and RVV RISC-V.
- Existing C fill/copy/blend parity gate: PASS.
- Exporter native execution now derives from instruction hits, not logical
  provider calls; generic RISC-V scalar fallback therefore remains false.

The tiny Simple AOT span probe still fails before linking because LLVM lowering
emits an `i32` operand into `icmp ne i64` for an array-length comparison. The
three-cycle cap was reached; the blocker is recorded in
`llvm_aot_array_len_comparison_width_mismatch_2026-07-10.md`. No full 4K/8K or
Cairo performance claim is made from this owner-only step.

## Next Step

Do not repeat the viewport/DPI/fallback/color proof work. Fix the focused LLVM
width mismatch, then use the in-place owner from explicit CPU-SIMD HTML solid
spans without routing shared GPU staging through it. Run the canonical combined
CPU-SIMD/scalar 4K/8K exporter once and require native instruction hits, exact
checksums, full physical dimensions, 300dpi, no size reduction, and no fallback.
Only then refresh the retained checksum contract and run the external Cairo
comparison once.
