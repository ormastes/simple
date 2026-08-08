# SimpleOS WM gate: content-provenance rejection is the last blocker after the boot-chain fixes

- Status: OPEN
- Date: 2026-08-04
- Lane: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (x86_64, OVMF pflash, macOS arm64 TCG host)
- Owner note: the rejecting code path is in the WM theme/provenance plumbing that has
  concurrent in-flight edits by another session (`src/os/compositor/shared_mdi_framebuffer_scene.spl`,
  `src/os/compositor/simple_web_window_renderer.spl`, cf. `ac5fd76af0 fix(simpleos): align wm
  theme snapshot identity plumbing`). Deliberately not fixed from this session.

## Where the gate stands now (2026-08-04, this machine)

Fixed this session (pushed as `177754a3ee` + follow-up):

1. Freestanding link fabrication (`rt_find` / `rt_native_cmp` / `rt_string_partition`) — implemented.
2. `browser_demo` build: `clang-20` hardcode + macOS `od` trailing-line bug — fixed.
3. GRUB/OVMF discovery on macOS in readiness + hello-lifecycle wrappers — fixed.
4. `sfnt.parse_fvar_axes` Option-match nil fault on the freestanding lane — fixed
   (`sfnt_fvar_option_match_nil_baremetal_2026-08-04.md`).
5. Guest heap exhaustion during 4K desktop bring-up: bump heap raised 512MB → 1GiB
   (no-free bump allocator; frame-arena reclamation remains the tracked real fix in
   `simpleos_bump_heap_no_free_interactive_session_2026-07-26.md`).
6. Readiness wait: hardcoded 60 s → `SIMPLEOS_WM_READINESS_TIMEOUT_MS` knob
   (default unchanged; TCG hosts need ~10-15 min for the 4K CPU-fallback layout).

Result: the guest now boots under OVMF, loads the pinned variable font from NVMe,
spawns Browser Demo / Hello World / Clang (`process-owned-surfaces-ready count=3`,
`launcher apps=15`), and composites at 3840x2160 (`host-gpu-fallback`).

## The remaining blocker

With `SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000` the run ends:

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=guest-render-fault
```

fired by `serial_has_production_fault` on:

```
[wm-frame] content-provenance-rejected window_id=3 status=engine2d_rendered backend=software fallback=none material= theme=aetheric_dark source=e13114ec328cce00747dec8565b1188a3e2f920817661d2c41bb4a347e0463cd
[wm-frame] window-degraded window_id=3 reason=unresolved-or-duplicate-content
```

Note `material=` is empty — the provenance record for window 3's engine2d-rendered
software surface carries no material identity, so the compositor rejects it and
degrades the window. No exception frames; this is a validation rejection, not a crash.

## Repro

```
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple \
SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000 \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Serial: `build/simpleos_wm_fullscreen_evidence/serial.log` (440 lines; rejection near the end).
