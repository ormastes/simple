# SimpleOS 2D render / WM QEMU evidence — 2026-08-07 (blocked before boot)

## Verdict (one line)

**QEMU-only lane, BLOCKED before boot**: the documented desktop-render evidence
gate (`check-simpleos-wm-fullscreen-evidence.shs`) failed at the native kernel
**build** step, before QEMU was ever launched. No OVMF boot, no PPM capture,
no SIMD/Vulkan engagement was exercised this run. The known PML4 blocker is
**not** the obstacle here — it is fixed and is unrelated to this build failure
(see below). This session did not produce fresh evidence that the 2D render
path runs on SimpleOS under QEMU; it produced a precise, reproducible build
blocker instead.

## What was attempted

Documented path located via `doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md`
(origin/main `caa216410893f3a4223b07ad5dd3074b17cb6e75`), item D.1/D.2 and the
2026-07-19 milestone entry, which point at
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` as the gate that
builds `gui_entry_desktop.spl` natively and boots it under **real OVMF pflash**
firmware (never `-kernel`, per `.claude/rules/board-runnable.md`, enforced at
the script's own line 726).

Command executed (foreground background-task, output captured):

```
SIMPLE_BIN=/home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
REPORT_PATH=<scratch>/simpleos_wm_fullscreen_evidence_run.md \
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS=900 \
SIMPLEOS_WM_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS=870 \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

`SIMPLE_BIN` was pinned explicitly to the pure-Simple self-hosted binary
(`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, version
`simple-bootstrap 1.0.0-beta`) — the project rule is "default tooling =
pure-Simple self-hosted binary, not the Rust seed," and the script itself
rejects a Rust-seed `SIMPLE_BIN` (line 402, `is_rust_seed_path`).

Host prerequisites confirmed present:
- `qemu-system-x86_64` 8.2.2 (Debian) — present.
- `/usr/share/OVMF/OVMF_CODE_4M.fd`, `/usr/share/OVMF/OVMF_VARS_4M.fd` — present.
- Font asset `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
  — present, 1,708,408 bytes (matches the script's pinned expectation).

## Result — build failure, transcript excerpt

Evidence env dump (`build/simpleos_wm_fullscreen_evidence/evidence.env`, this run):

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=wm-simple-web-build-failed
simpleos_wm_fullscreen_kernel_build_status=failed-cache-preserved
simpleos_wm_fullscreen_serial_log_bytes=0
```

`serial_log_bytes=0` is the load-bearing line: QEMU never produced any serial
output because it was never launched — the native build of the kernel closure
aborted first.

Native build log (`build/simpleos_wm_fullscreen_evidence/native-build.out`,
this run, verbatim):

```
FAILED FILES (2):
  - src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl =>
    hir: Unsupported feature: cannot infer field type while lowering
    SimpleWebEngine2DStaticPixelCache.retain_result_for_html: struct
    'SimpleWebLayoutEngine2DReadbackResult' field 'resolved_backend'
  - src/lib/gc_async_mut/ui/web_render_pixel_backend.spl =>
    hir: Unsupported feature: cannot infer field type while lowering
    _web_render_label_backend: struct 'SimpleWebLayoutEngine2DReadbackResult'
    field 'resolved_backend'

Build failed: native-build aborted: 2 file(s) failed to compile
```

This is a **fresh, independently reproduced** failure, not a stale artifact:
the same two files failed the same way in a prior local run recorded at
`build/simpleos_wm_fullscreen_evidence/evidence.env` (timestamped 2026-08-06
16:16, before this session's run), and this session reproduced it again from
a clean invocation with an explicit non-seed `SIMPLE_BIN`.

## Root cause identified (not filed as a bug before this report)

`SimpleWebLayoutEngine2DReadbackResult.resolved_backend`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:75,
101, 128, 152, 179, 207-208`) is a field the pure-Simple self-hosted
compiler's HIR lowering cannot infer a type for when compiling
`SimpleWebEngine2DStaticPixelCache.retain_result_for_html` and
`_web_render_label_backend` (`src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`).
The field was introduced by commit `ca75bf0700a` ("fix(web-render): label an
artifact with the backend that produced its pixels", 2026-08-05) to
disambiguate two independent "which engine2d backend rendered this" resolvers.
`git grep resolved_backend` across `doc/08_tracking/bug` and the rest of
`doc/` (as of origin/main `caa216410893f3a4223b07ad5dd3074b17cb6e75`) finds no
existing bug record for this HIR type-inference failure — it is undocumented.

Because `browser_engine`/`web_render_pixel_backend` are pulled into the
desktop kernel's native-build closure (transitively, via the shared UI/WM
library graph), this single HIR gap is enough to block the entire
`gui_entry_desktop.spl` kernel build, and therefore blocks every downstream
step of the 2D-render QEMU evidence gate: no kernel artifact, no boot, no PPM
capture, no SIMD/Vulkan engagement to observe.

**This report does not fix the compiler bug** — no `src/**` changes were made
per this task's scope (evidence/verification unit only). Recommend filing
`doc/08_tracking/bug/hir_lowering_cannot_infer_resolved_backend_field_type_2026-08-08.md`
against the pure-Simple self-hosted compiler's HIR lowering pass, owner path
`src/compiler/**` (HIR/type-inference layer), citing the two failing files
above and commit `ca75bf0700a` as the introducing change.

## PML4 blocker status (per task's explicit ask)

**FIXED, and not implicated in this failure.** Per
`doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`
on origin/main: the two-VMM-implementation wiring bug was fixed 2026-08-06,
verified by a positive marker (`[VMM] portable VMM published kernel PML4
0x402718720`, `[spawn] parsed entry=...`, `persist /hello.o -> OK`,
`exit status=0`), plus a passing interpreter-level regression spec
(`test/01_unit/os/kernel/memory/vmm_publish_kernel_pml4_spec.spl`, 3/3, with a
sabotage check confirming the spec is load-bearing). The doc's one open
residual ("L5") is a **separate** 4 MiB hard-fail bound in the SSH
`getfile`/`_scp_read_file_bytes` chain (`ssh_session.spl:237`) used by the
in-guest clang self-compile lane — it has nothing to do with `gui_entry_desktop.spl`
booting or rendering. The desktop-render lane (per the 2026-07-19 milestone
recorded in `wm_window_render_api_hardening_plan.md`) does not perform FS-exec
ring-3 spawn at all; it boots directly to `first-frame-rendered` in kernel
context. **Conclusion: even if this run had reached QEMU, the PML4 defect
would not have blocked it** — the two issues are on independent code paths.

## SIMD / Vulkan engagement

**Not observed — could not be, since QEMU never ran.** For context (from the
plan doc, not from a fresh run): the SimpleOS desktop lane is pinned to
`backend=baremetal-framebuffer`, a CPU rasterizer
(`src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl`). There is no
Vulkan backend in the SimpleOS baremetal target — Vulkan/CUDA/Metal engine2d
backends (`backend_accel_vulkan.spl`, `backend_cuda*.spl`, etc.) are
host-side/library-layer only. This session's blend-span SIMD kernel work is
also host/library-layer; nothing in the recorded evidence chain shows those
SIMD kernels executing inside a booted SimpleOS guest.

## Board-runnable caveat

This entire evidence attempt, had it succeeded, would have been **QEMU-only**:
the documented gate boots via OVMF pflash (real-firmware proxy, compliant with
`.claude/rules/board-runnable.md`), which is the correct *proxy*, but no
physical-board boot/run was attempted or claimed. Per the 2026-07-19 milestone
in the plan doc, a prior run did reach `COVERAGE 3840x2160 nonblack=99.83%`
under **both** QEMU `-kernel` and OVMF pflash with NVMe attached — that is the
most recent point at which this lane is recorded as having actually rendered.
This session could not reproduce or extend that evidence; the build blocker
above must be fixed first.

## Unblock condition

1. File and fix the HIR lowering gap for `SimpleWebLayoutEngine2DReadbackResult.resolved_backend`
   in the pure-Simple self-hosted compiler (owner: compiler/HIR-lowering
   maintainer, not this UI/OS wave).
2. Re-run `sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs` with an
   explicit non-seed `SIMPLE_BIN` (as in this report) once (1) lands.
3. If it boots, check the serial log for zero `[spawn]`/`FAIL user-AS` lines
   (confirms the PML4 fix holds and is irrelevant to this lane) and for the
   `backend=baremetal-framebuffer` banner (confirms CPU-rasterizer, non-Vulkan
   status, unless a Vulkan backend has since been wired into this entry point).

## Evidence artifacts (local, not landed — build/ is gitignored)

- `build/simpleos_wm_fullscreen_evidence/evidence.env` (this run)
- `build/simpleos_wm_fullscreen_evidence/native-build.out` (this run)
- Full stdout: `/home/ormastes/.claude/jobs/afa73365/tmp/fullscreen_run_stdout.log`

## Fix + re-run — 2026-08-08

### Root cause was more specific than "cannot infer type"

The class `SimpleWebLayoutEngine2DReadbackResult`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:80-96`)
never declared a `resolved_backend` field. Commit `ca75bf0700a` added
`.resolved_backend` reads in `simple_web_engine2d_renderer.spl` and
`web_render_pixel_backend.spl`, and set it at exactly ONE of the struct's
four constructor call sites
(`simple_web_engine2d_renderer.spl:179`) — but never added the field to the
class declaration, and never set it at the other three constructors
(`simple_web_layout_engine2d_fast.spl:727, 743, 763`). The frontend accepted
this silently; the failure surfaced only in HIR lowering as "cannot infer
field type," naming a consumer function rather than the real defect site.

### Fix applied (source-only)

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`:
- Added `resolved_backend: text` to the `SimpleWebLayoutEngine2DReadbackResult`
  class declaration.
- Added `resolved_backend: backend_name` to all three previously-incomplete
  constructor call sites (lines 727, 743, 763 pre-edit) — `backend_name` is
  the parameter already in scope at each site and matches the semantics used
  by the one constructor that already set the field correctly.

Bug filed for the misleading/late diagnostic (frontend does not catch a
field that is read/set at some constructors and declared nowhere):
`doc/08_tracking/bug/hir_lowering_cannot_infer_struct_field_type_from_constructor_args_only_2026-08-08.md`.

### Re-run result: original blocker cleared, kernel build now fails LATER (link stage)

Command (same as the original run, `SIMPLE_BIN` re-pinned to the pure-Simple
self-hosted binary):

```
SIMPLE_BIN=/home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
REPORT_PATH=<scratch>/simpleos_wm_fullscreen_evidence_run.md \
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS=900 \
SIMPLEOS_WM_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS=870 \
timeout 840 sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

`native-build.out` no longer contains any `hir:`/`resolved_backend` error —
the two previously-failing files
(`simple_web_engine2d_renderer.spl`, `web_render_pixel_backend.spl`) now
compile. The build progressed all the way through HIR lowering/codegen for
the full `gui_entry_desktop.spl` closure to the **freestanding link stage**,
where it hit a **different, pre-existing, unrelated blocker**:

```
Freestanding unresolved symbol check: 130 unexpected symbol(s)
Fabricated freestanding stubs: 130 symbol(s) for entry
'simpleos_wm_production_desktop.elf.candidate' -- weak bodies that RETURN 0
(baseline config/freestanding_fabricated_stub_baseline.sdn: 117 known, 13 new)
...
Build failed: freestanding link would FABRICATE 13 symbol(s) not in the
baseline for entry 'simpleos_wm_production_desktop.elf.candidate':
hda_dma_write_pcm_i16, rt_clear, rt_cuda_memset_d32,
rt_engine2d_simd_blend_const_span_u32, rt_engine2d_simd_blend_span_u32,
rt_metal_device_identity, rt_metal_device_supports_metal3,
rt_metal_load_library_bytes, rt_metal_load_library_bytes_raw,
rt_metal_load_library_file, rt_pop, rt_push, rt_sort. These get weak bodies
that return 0, which silently corrupts every caller. Implement them, or --
only if nil is genuinely the correct answer -- re-baseline with
SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1 and justify it in
config/freestanding_fabricated_stub_baseline.sdn.
```

`evidence.env` this run:

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=wm-simple-web-build-failed
simpleos_wm_fullscreen_kernel_build_status=failed-cache-preserved
simpleos_wm_fullscreen_serial_log_bytes=0
```

**Verdict: the `resolved_backend` HIR blocker is fully cleared — it is not
the reason the gate fails anymore.** The gate still does not reach QEMU
(`serial_log_bytes=0`, no OVMF boot this run) — it is now blocked by a
separate, freestanding-link fabricated-stub gate rejecting 13 new
unimplemented runtime symbols (SIMD engine2d blend spans, Metal device
query/library-load, CUDA memset, array `push`/`pop`/`sort`/`clear`
primitives, and an HDA PCM DMA write helper) that this closure now reaches
for the first time. This is out of scope for the smallest-safe-fix requested
here (13 real runtime implementations, several touching hardware-specific
backends); it is the concrete next blocker for whoever picks up the
QEMU-boot evidence gate next. No `doc/08_tracking/bug/` record filed for it
in this pass — recommend one be filed against `src/runtime/**` /
`src/lib/**` for the 13 named symbols before attempting
`SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1` (a baseline bump would silently
accept "return 0" bodies for real GPU/audio/array primitives, which the gate
itself warns "silently corrupts every caller").

## 7 of 13 fabricated-stub symbols implemented, gate narrows to 6 — 2026-08-08

### Per-symbol root cause (traced via `nm -u` on the actual failed-run objects)

`build/simpleos_wm_fullscreen_evidence/native-objects-*/*.o` from the prior
failing run were still on disk. `nm`-ing all 772 objects and matching each of
the 13 symbols against real `U` (undefined) entries — not just `declare`
text in the LLVM backend prelude — confirmed all 13 are genuinely CALLED
somewhere in the compiled closure, not dead references a `declare`-only scan
would over-count:

| Symbol(s) | Referencing object | Root cause |
|---|---|---|
| `rt_push`, `rt_pop`, `rt_sort`, `rt_clear` | many (`mod_148`=`dom_color.spl`, `mod_346`=`stmt_cache.spl`, others) | Type-blind `.push()`/`.pop()`/`.sort()`/`.clear()` method dispatch (`compiler/src/codegen/instr/calls.rs`) routes to these receiver-polymorphic helpers everywhere an array (or text) method is called. They exist for hosted builds (`src/runtime/runtime_native.c:4297/6857/6893`, `rt_push` only in the Rust runtime `value/collections.rs:2885`) but the freestanding link is `-nostdlib` and never sees `runtime_native.c` (`linker.rs:1009`) — no freestanding body existed anywhere. Genuinely needed: pervasive array-method dispatch, not eliminable. |
| `rt_engine2d_simd_blend_span_u32`, `rt_engine2d_simd_blend_const_span_u32` | `mod_378` = `lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl`, called from `simd_isa_provider.spl` | Real CPU-software-rasterizer SIMD span blend, reached from `backend_software.spl` (the CPU path `backend_baremetal.spl` uses). Sibling functions (`fill_span`, `copy_span`, `blend_row`) already had freestanding C bodies in `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`; only these two straight-alpha span blends were missing. Genuinely needed, not dead code. |
| `hda_dma_write_pcm_i16` | `mod_714` = `os/services/audio/audio_service.spl` | `gui_entry_desktop.spl` imports `os.services.audio.audio_service` directly and unconditionally logs audio-offload status on every boot (`gui_entry_desktop.spl:368-370`) — a real, always-executed entry-point code path, not something eliminable by conditional compilation. Deeper finding: `hda_dma_write_pcm_i16` was declared/imported by `audio_service.spl` (`use os.drivers.audio.hda_dma_resources.{...}`) but **never implemented or even exported anywhere in the tree** — a pre-existing missing-implementation bug in the HDA driver, not freestanding-specific. |
| `rt_cuda_memset_d32`, `rt_metal_device_identity`, `rt_metal_device_supports_metal3`, `rt_metal_load_library_bytes`, `rt_metal_load_library_bytes_raw`, `rt_metal_load_library_file` | `mod_342` = `lib/nogc_sync_mut/cuda/mod.spl`, `mod_386` = `lib/nogc_sync_mut/io/metal_sffi.spl` | `src/lib/gc_async_mut/gpu/engine2d/mod.spl` (the engine2d package barrel) unconditionally `use`s **every** backend implementation — `backend_cuda`, `backend_metal`, `backend_vulkan`, `backend_opengl`, `backend_directx`, etc. — regardless of which backend is actually selected at runtime (`backend_baremetal` for this target). These host-only GPU-driver FFI bridges (macOS Metal, NVIDIA CUDA) are unreachable at runtime on this baremetal-framebuffer x86_64 kernel but are still compiled into the closure at build time. **This is pre-existing, already-accepted architectural debt**: `config/freestanding_fabricated_stub_baseline.sdn` already carries sibling symbols from the exact same families for the exact same entry (`rt_cuda_ctx_set_current`, `rt_cuda_launch_kernel_name`, `rt_cuda_module_load_data_bytes`, `rt_cuda_shutdown`, `rt_metal_destroy_command_buffer`, `rt_metal_run_compute_frame`, lines 87-90/117-118) — these 6 are simply the same class of symbol, newly surfaced by today's declare/backend additions (`796d8484`). |

### Fixes landed (source-only, real implementations, not stubs)

- `src/os/drivers/audio/hda_dma_resources.spl`: implemented
  `hda_dma_write_pcm_i16` (writes interleaved i16 PCM samples into the
  `HDA_DMA_PCM` ring at a given frame offset via `rt_ptr_write_i16`, bounded
  to the buffer size, returns frames actually written) — filled in a
  genuinely-missing driver primitive, not freestanding-specific.
- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`:
  added freestanding C bodies for `rt_push`, `rt_pop`, `rt_clear`, `rt_sort`
  (ported from `runtime_native.c`'s array/text receiver-dispatch semantics,
  adapted to this file's tagged `RuntimeValue`/`HEAP_ARRAY`/`HEAP_STRING`
  representation) and `rt_engine2d_simd_blend_span_u32`,
  `rt_engine2d_simd_blend_const_span_u32` (ported from
  `runtime_simd_dispatch.c:1628/1649`, reusing this file's existing
  `_bm_pixel_array_from_abi`/`_bm_span_bounds`/`_bm_blend_pixel` helpers that
  the sibling `fill_span`/`copy_span`/`blend_row` functions already used).
  `gcc -fsyntax-only -ffreestanding -nostdlib` on the edited file is clean.

### Verification: re-ran the exact evidence-gate command

```
SIMPLE_BIN=/home/ormastes/dev/pub/simple/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple \
REPORT_PATH=<scratch>/simpleos_wm_fullscreen_evidence_run2.md \
BUILD_DIR=build/simpleos_wm_fullscreen_evidence2 \
SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS=900 \
SIMPLEOS_WM_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS=870 \
timeout 840 sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

`native-build.out`:

```
Freestanding unresolved symbol check: 123 unexpected symbol(s)
Fabricated freestanding stubs: 123 symbol(s) for entry
'simpleos_wm_production_desktop.elf.candidate' -- weak bodies that RETURN 0
(baseline config/freestanding_fabricated_stub_baseline.sdn: 117 known, 6 new)
...
Build failed: freestanding link would FABRICATE 6 symbol(s) not in the
baseline for entry 'simpleos_wm_production_desktop.elf.candidate':
rt_cuda_memset_d32, rt_metal_device_identity, rt_metal_device_supports_metal3,
rt_metal_load_library_bytes, rt_metal_load_library_bytes_raw,
rt_metal_load_library_file.
```

`evidence.env`: `simpleos_wm_fullscreen_status=fail`,
`simpleos_wm_fullscreen_reason=wm-simple-web-build-failed`,
`simpleos_wm_fullscreen_serial_log_bytes=0` — the gate still does not reach
QEMU this run. **All 7 targeted symbols dropped out of the unresolved set**
(13 -> 6); the 7 rejected before are gone from the "new" count, confirming
the freestanding link now resolves them for real, not via a baseline bump
(none of the 7 were added to `config/freestanding_fabricated_stub_baseline.sdn`).

### Next blocker (precise, not fixed this pass)

The remaining 6 (`rt_cuda_memset_d32` + 5 `rt_metal_*`) require a real
conditional-compilation fix at `src/lib/gc_async_mut/gpu/engine2d/mod.spl`
(lines 108-121): the backend barrel currently `use`s every GPU backend
unconditionally. Making that target-conditional is a cross-cutting change —
`engine2d.mod` is consumed by every engine2d-using build (macOS Metal apps,
CUDA apps, the SimpleOS baremetal kernel), so gating imports by target
risks breaking non-kernel consumers and needs its own scoped session, not a
fold-in here. Per this task's explicit instruction, these 6 were **not**
re-baselined as an accepted-stub cover-up, even though
`config/freestanding_fabricated_stub_baseline.sdn` already carries sibling
CUDA/Metal symbols for this exact entry (lines 87-90, 117-118) — that
precedent explains why the compiler correctly refuses to fabricate them
silently, not a license to extend it further from this session.

Recommend filing `doc/08_tracking/bug/engine2d_mod_barrel_imports_all_gpu_backends_unconditionally_2026-08-08.md`
against `src/lib/gc_async_mut/gpu/engine2d/mod.spl`, scoped to: introduce a
target-conditional backend-selection surface (or split `mod.spl`'s barrel
import into a per-target subset) so a baremetal-framebuffer kernel build
does not compile in macOS Metal / NVIDIA CUDA host-driver FFI bridges it can
never reach at runtime.

Board-runnable caveat unchanged from the section above: this remains a QEMU
real-firmware-proxy (OVMF pflash) evidence path; no physical-board attempt
was made or claimed in this pass either.

## Root-cause correction: the fix site above is wrong — `mod.spl` is not in the closure — 2026-08-08

Traced the 6 remaining symbols to the actual build objects still on disk
(`build/simpleos_wm_fullscreen_evidence2/native-objects-K0fOB0/`, 774
objects) via `nm -u`/`nm`, rather than inferring from source text:

```
mod_183.o: V lib__gc_async_mut__gpu__engine2d__backend_cuda__CudaBackend
mod_194.o: V lib__gc_async_mut__gpu__engine2d__backend_metal__MetalBackend
mod_223.o: U lib__gc_async_mut__gpu__engine2d__backend_cuda__CudaBackend
mod_158/160/171/219/220/261/262/492/497/498.o:
    U lib__gc_async_mut__gpu__engine2d__engine__Engine2D
```

**No object in this closure contains any `engine2d__mod__` symbol.** The
package barrel `src/lib/gc_async_mut/gpu/engine2d/mod.spl` is not part of
the compiled closure for this kernel entry at all — the prior "Next
blocker" section above, which attributed the 6 symbols to `mod.spl` lines
108-121, is corrected: the real culprit is
`src/lib/gc_async_mut/gpu/engine2d/engine.spl`. Its `Engine2D` facade class
unconditionally imports `backend_cuda`/`backend_metal` (lines 38, 52) and,
more importantly, declares `cuda_backend: CudaBackend?` /
`metal_backend: MetalBackend?` as **struct fields** (lines 230, 234) with
six method-body call sites (435, 533, 552, 611, 770, 812). The kernel's
actual import chain — `gui_entry_desktop.spl` →
`os.compositor.compositor_engine2d.{Engine2dCompositorBackend}` →
`use std.gpu.engine2d.engine.{Engine2D}` — already bypasses `mod.spl`
entirely (as does `engine2d_display.spl`); it pulls in the full `Engine2D`
type directly.

This also means a target-conditional `use`-import gate — even if the
compiler had one, and it confirmed it does not (`@cfg(x86_64/arm64/riscv64)`
is the only mechanism found, and it is arch-dispatch for top-level function
bodies only, not applicable to `use` statements or struct fields) — would
not have fixed this: struct fields on a shared class can't be removed by
gating an import. A real fix needs either (a) splitting `Engine2D` into a
lean baremetal variant without the two GPU-backend fields, or (b) real
freestanding bodies for the 6 symbols that correctly report "device absent"
on this target (unlike a fabricated 0-returning stub, a real absent-device
answer is semantically correct here). Neither was attempted this pass — see
`doc/08_tracking/bug/engine2d_mod_barrel_imports_all_gpu_backends_unconditionally_2026-08-08.md`
for the full trace and the two candidate fixes. No source was changed, so
the evidence gate was not re-run; it would reproduce the same 6-symbol
failure already recorded above.
