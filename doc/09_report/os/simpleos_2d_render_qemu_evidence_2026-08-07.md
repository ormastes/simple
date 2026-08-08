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
