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

## Re-verification (2026-08-10)

Fresh gate re-run confirms the table above is unchanged: `check-kv260-simpleos-boot-release.shs`
still `BLOCKED reason=bitstream-missing:build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit`
(now reports `BLOCKED` rather than a bare `SKIP`, exit 0, but still states
"NOTHING was checked" — the vacuous-pass gate defect noted below is unchanged).

**Hardware-presence correction, stated plainly per `.claude/rules/board-runnable.md`:**
this host is NOT hardware-free. `lsusb`/`udevadm` confirm a real, physically
attached Xilinx **ML Carrier Card (FT4232H Quad UART/JTAG, serial
`XFL1OSWWFM2B`)** exposing `/dev/ttyUSB0`-`/dev/ttyUSB3` — the carrier board
used for Kria K26/KV260 bring-up per `doc/07_guide/hardware/fpga/
kria_k26_ml_carrier_bringup.md`. So the earlier framing ("no board evidence
exists at all") is accurate only in the narrow sense that no boot/serial
*transcript* exists yet — it is not because hardware is absent. The actual
blocker is a missing **build artifact**: `k26_rv32_ddr.bit` (an FPGA
bitstream) has never been synthesized on this host, and Vivado bitstream
synthesis is a multi-hour job, not something this pass's scope covers. This
correction does not change the doc's bottom line (still no board-runnable WM
evidence) but it changes *why*: reachable hardware + missing bitstream build,
not missing hardware. Producing that bitstream and a subsequent real
boot/serial transcript is the concrete unblock step and remains out of scope
for this triage pass; leaving it filed here rather than silently implying
either "no hardware" or "board-runnable."

Status remains **OPEN**, unchanged in substance from 2026-08-08 — this
re-verification only sharpens the hardware-availability claim with fresh
evidence from this host and confirms no gate result has drifted.

## Addendum (2026-08-10, evening pass): tonight's rung-(c)/(d) WM work is QEMU-only, unfiled scope gap in the run plan

Tonight's session ran the x86_64 OVMF-pflash SimpleOS WM lane further than the
2026-08-08 table shows: it reached **rung (c)** — boots and renders 3 windows
with a real font under real-firmware OVMF pflash (not `-kernel`, not
`isa-debug-exit`, consistent with the rule) — with a **rung (d)** attempt
(real PPM screendump proving actual rendered pixels) in progress on a separate
agent at the time of this triage. Budget discipline for this pass ruled out
running a build/QEMU pass to independently re-locate the exact artifact paths
tonight's agent produced (see `.spipe/simple-wm-host-simpleos-fullscreen/state.md`
for the live work item); that gap is noted here rather than silently assumed
away.

This is unambiguously still QEMU-only under the rule: no board boot, no serial
transcript, no board identity claim accompanies tonight's rungs (c)/(d). What
is new versus 2026-08-08 is *why* it stayed QEMU-only. The task's own run-plan
document, `.spipe/simple-wm-host-simpleos-fullscreen/state.md`, states under
"Scope Exclusions": *"Physical-board display evidence and unrelated SimpleOS
driver completion are excluded; SimpleOS runtime proof is QEMU framebuffer
evidence unless a board lane is explicitly selected later."* That is a
**plan-authored** QEMU-only scoping, not a user-authored one. Per
`.claude/rules/board-runnable.md`, only an explicit **user** statement may
scope work to QEMU-only ("Scope to QEMU-only only when the user says so") — no
such user instruction is on record for tonight's WM work. The plan's own scope
exclusion is therefore itself an instance of the drift the rule exists to
prevent, independent of whether rungs (c)/(d) individually succeed.

**Board-availability status, reconfirmed:** as recorded above (2026-08-10
re-verification), this host is not hardware-free — a physically attached
Xilinx ML Carrier Card (KV260/K26 family) is present at `/dev/ttyUSB0`-`3`.
The blocker for a board attempt is a missing FPGA bitstream build
(`k26_rv32_ddr.bit`, multi-hour Vivado synthesis), not absent hardware, and not
architecturally related to tonight's x86_64 OVMF work (the KV260 lane is
RV32/Kria, a different target entirely from tonight's x86_64 WM lane).

**EFI-stub gap relevance check:** the rule's aarch64 EFI-stub gap
(`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`)
is unrelated to tonight's evidence. Tonight's rung-(c)/(d) work is x86_64 only,
booted via OVMF pflash, which already has a working real-firmware path (see
`doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`); the
aarch64 EFI-stub gap does not block or bear on it. It remains open and
accurately described for the aarch64 lane specifically, unchanged by tonight's
work.

**Verdict for tonight's work:** QEMU-only, correctly so under the rule's
"say so explicitly and file it" clause for hardware genuinely gated on a
missing bitstream build — but the plan document's self-authored scope
exclusion should be corrected to either (a) obtain explicit user sign-off to
stay QEMU-only, or (b) add the board lane as a tracked, currently-blocked next
step referencing this bug file, rather than silently excluding it in the plan.
Filed here as an addendum rather than a new bug file, since it is the same
underlying gap this document already tracks.

## Related

- `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §7 (lanes U0–U3)
- `.claude/rules/board-runnable.md`
- `.spipe/simple-wm-host-simpleos-fullscreen/state.md` (tonight's rung-(c)/(d) work item; scope-exclusion language flagged above)
