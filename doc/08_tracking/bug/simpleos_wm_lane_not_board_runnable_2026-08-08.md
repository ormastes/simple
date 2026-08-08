# SimpleOS WM/render lane is component-evidence only — not an integrated runnable WM, not board-runnable

Date: 2026-08-08
Status: OPEN
Rule invoked: `.claude/rules/board-runnable.md`

## Verdict

There is **no SimpleOS image in which a window manager runs and renders**, on
QEMU or on hardware. Every SimpleOS-facing WM gate either fails closed for a
missing prerequisite or is a preflight/readiness probe that never boots
anything. Component-level evidence (hosted/GTK capture, renderer unification)
also currently fails.

## Gate results (run 2026-08-08, this host)

| gate | verbatim verdict line | exit | class |
|---|---|---|---|
| `check-simpleos-wm-aqua-glyph-ovmf-evidence.shs` | `wm_aqua_glyph_ovmf_evidence: not-ready` / `reason: SIMPLEOS_KERNEL_ELF is not set` | 1 | BLOCKED (fails closed, correct) |
| `check-simpleos-arm64-wm-qemu-readiness.shs` | `arm64_wm_qemu_readiness: ready` | 0 | PASS — **preflight only** (qemu present, ramfb device, dry-run parse). Boots nothing, renders nothing. |
| `check-simpleos-x86-64-wm-qemu-readiness.shs` | `guide_gap: false (...)` | 0 | PASS — preflight/doc only |
| `check-simpleos-x86-64-wm-render-event-evidence.shs` | `simpleos_wm_fullscreen_reason=wm-simple-web-build-source-changed`, `disk_image_status=not-staged`, `kernel_sha256=` (empty), `serial_log_bytes=0` | 1 | FAIL (kernel never built, QEMU never started) |
| `check-hosted-wm-capture-evidence.shs` | `hosted_wm_capture_reason=capture-program-failed` | 1 | FAIL |
| `check-shared-wm-renderer-unification-evidence.shs` | `shared_wm_renderer_unification_reason=logic-check-failed` | 1 | FAIL |
| `check-kv260-simpleos-boot-release.shs` | `STATUS: SKIP kv260-simpleos-boot-release reason=bitstream-missing:build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit (board lane not executed on this host)` | 0 | **VACUOUS** — exits 0 having checked nothing. See "Gate defects". |
| `check-freebsd-wm-seam-refusal.shs` | `FREEBSD WM SEAM VERDICT: platform=freebsd refusal=blocked reason=QEMU failed to start` | 1 | BLOCKED |

## Integration rungs actually reached

- **(a) source present — YES.** `examples/09_embedded/simple_os/arch/{arm64,x86_64}/gui_entry_desktop.spl`,
  `src/os/kernel/arch/arm64/ramfb.spl`.
- **(b) cross-built / staged into an image — NO.** x86_64:
  `simpleos_wm_fullscreen_kernel_sha256=` is empty and
  `simpleos_wm_fullscreen_disk_image_status=not-staged`. No WM kernel ELF exists.
- **(c) booted under real firmware — PARTIAL, and WITHOUT a WM.** The only real
  SimpleOS boot artifact on this host is the aarch64 Limine/AAVMF lane:
  `build/os/aarch64_limine/kernel.elf` (92,592 bytes) with
  `build/os/aarch64_limine/serial.log` ending
  `[BOOT] SIMPLEOS-AARCH64-LIMINE-KERNEL-OK`. That same log contains
  `[BOOT] WARNING: No framebuffer response from Limine` and
  `[BOOT] memory_init: MILESTONE STUB — Layer 1 not yet ported to the Limine boot lane (aarch64)`.
  A kernel that gets no framebuffer cannot host a compositor.
- **(d) WM actually running and rendering in-guest — NO.** No screendump, no
  serial marker, no PPM from any SimpleOS WM boot. Every WM PPM under `build/`
  (`build/tmp/wm_showcase/*`, `build/wm_host_seam/seam-display.ppm`, game2d/3d
  captures) is a **host-side** render, not in-guest SimpleOS.

## Board-runnable gap (`.claude/rules/board-runnable.md`)

Stated plainly, as the rule requires:

- **QEMU side:** only *readiness* (arm64/x86_64 preflight) exists. No QEMU boot
  of a WM has occurred. The aqua gate is correctly wired for real firmware
  (OVMF pflash, explicit "NEVER -kernel, NEVER isa-debug-exit" in its header)
  but has never had an input kernel to run.
- **Physical board side:** **no board evidence exists at all.** No board
  identity, no download/boot path transcript, no serial or SSH transcript for a
  WM on hardware. The KV260 lane cannot run here (`k26_rv32_ddr.bit` absent).
- Per the rule this is a **defect, not a completion**, and is filed here rather
  than implied.

## Gate defects

1. **FIXED this pass** — `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs:20`
   tested `[ ! -x "$CANONICAL_WRAPPER" ]` against
   `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`, which is mode
   `0664` in this repo (most `.shs` gates are). The gate therefore reported
   `reason=canonical-wrapper-missing:` for a file that exists, masking the real
   x86_64 verdict behind a phantom cause. Changed to `-f` + `exec sh`, matching
   how every other caller invokes `.shs` files. The real verdict (table above)
   only became visible after this fix.
2. **OPEN — vacuous pass.** `scripts/check/check-kv260-simpleos-boot-release.shs`
   exits **0** on `reason=bitstream-missing`. A gate that examined zero items
   must not exit 0; per `.claude/rules/vcs.md` verdict conventions this should
   be `ERROR — nothing was checked` / exit 2, so a board lane that never ran
   cannot be aggregated as a pass. Not changed here because other lanes may
   currently depend on its exit-0 skip semantics; changing it needs a sweep of
   its callers.

## Unblock condition

x86_64 WM evidence is gated on one artifact:
`build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`.
The wrapper refuses to reuse its cache because the recorded source revision
(`kernel_source_revision_sha256=cd56d7356f86d6d1094a7b08354ed4eb4abe5556cef33ae573bd6143afb1281e`)
no longer matches the tree — it emits `wm-simple-web-build-source-changed` at
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs:628` and preserves the
stale cache rather than silently passing. Correct behaviour; it just means the
kernel must be rebuilt.

Resume command (expect a long native build; `native_build_timeout_seconds=900`):

```sh
sh scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs
```

Only once that yields a non-empty `kernel_sha256` can the aqua/OVMF gate run:

```sh
SIMPLEOS_KERNEL_ELF=build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf \
SIMPLEOS_FONT_DISK=<font-disk.img> \
  sh scripts/check/check-simpleos-wm-aqua-glyph-ovmf-evidence.shs
```

Board-runnable then requires a third, currently unstarted step: the same kernel
built for and booted on real hardware with a serial transcript.

## Related

- `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §7 (lanes U0–U3)
- `.claude/rules/board-runnable.md`
