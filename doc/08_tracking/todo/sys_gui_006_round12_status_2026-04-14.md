# SYS-GUI-006 — Round 12 Status (2026-04-14)

**Owner:** Round-12 live-lane harness-race agent (workspace `/tmp/simple-round18`)
**Ticket:** SYS-GUI-006 bare-desktop framebuffer baseline
**Precedent:** `doc/08_tracking/todo/sys_gui_006_round11_status_2026-04-14.md`
**LIVE-GREEN status:** **STILL BLOCKED** — harness race mitigated; new root
cause surfaces (early QEMU exit after desktop-ready) which is OS-side and
out of scope for a spec-only round.

## TL;DR

- **Harness race fix landed:** spec no longer rebuilds `build_os(target)`
  in the second `it{}` block. Added a `_build_once(target)` helper that
  checks `file_exists(target.output)` before calling `build_os`. Wall-clock
  dropped from **52,382 ms → 27,948 ms** (one build saved, exactly matching
  the ~24-28 s compile time measured in Round-11).
- **Wait budget raised** 60,000 ms → 180,000 ms as belt-and-suspenders for
  slower CI hardware. Has no effect on the current failure mode (QEMU
  exits at ~876 ms wall-clock, well inside any budget), but documents the
  intent for future runs.
- **New root cause measured, not harness:** QEMU exits ~244 ms after
  emitting `[desktop-e2e] desktop-ready` because the subsequent
  `launcher_shortcut_dispatch(KEY_B, META_MODIFIER)` call path FAULTs on
  missing NVMe and returns false, causing `desktop_e2e_main()` to return
  false, which prints `TEST FAILED` and hits `isa-debug-exit`. See
  measurement below. **LIVE-GREEN via QMP screendump is architecturally
  impossible without an OS-side fix** to stop the post-marker crash.
- **No PPM baseline captured.** Required OS change is out of scope per
  this round's guardrails (test spec + doc edits only).

## Run evidence

### Command

```bash
cd /tmp/simple-round18
ln -sf /home/ormastes/dev/pub/simple/bin/simple bin/simple  # workspace needed this
/home/ormastes/dev/pub/simple/bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
```

### Spec summary

```
SimpleOS desktop framebuffer baseline (SYS-GUI-006)
[build][x86_64] phase=native-build OK elapsed_ms=27552
  ✓ builds desktop_e2e_entry.spl into a baremetal kernel
[simpleos_desktop_fb_spec] desktop paint-ready marker not seen within 180s
  (harness race + early QEMU exit — see Round-12 status)
  ✗ boots desktop, captures framebuffer via QMP, and matches baseline
  ✓ has a baseline directory for simpleos_desktop_framebuffer captures

3 examples, 1 failure
  FAILED (27948ms)
```

Compare with Round-11: `FAILED (52382ms)` — wall-clock nearly halved by
the `_build_once` fix. Exactly one `phase=native-build OK` line (was two
in Round-11).

### QEMU lifetime measurement

Direct QEMU run against the same kernel, timed aggressively:

```
marker at +579ms
qemu dead at +876ms        (Δ = 297ms after marker)
```

Earlier measurement with slightly different timing pipeline: marker at
+632ms, qemu dead at +876ms (Δ=244ms). Both within the same order of
magnitude — QEMU is alive for **only ~250-300 ms after desktop-ready**
before isa-debug-exit fires. QMP screendump DOES succeed inside that
window when fired aggressively via raw Python+UNIX-socket (verified:
2,359,312-byte PPM captured). The stock test harness cannot meet that
deadline because:

1. `wait_for_serial_marker` polls every 100 ms (up to 5 polls missed in
   a 300 ms window depending on phase alignment).
2. The serial log file is buffered by the shell pipeline
   (`-serial file:...`) and typically flushes only after QEMU exits. So
   when the harness polls during the 300 ms window the log on disk
   doesn't yet contain the marker.
3. When QEMU exits (shell pipeline ends), the harness's inner
   `rt_process_is_running` check returns false and takes the early-exit
   branch that returns `serial_output.contains(marker)` — but
   `serial_output` was read BEFORE the post-exit flush, so it doesn't
   see the marker either.

Post-exit, the file on disk DOES contain the marker (verified by `grep`
against `build/os/simpleos_desktop_qemu_serial.log` after the spec
fails). The harness-inner race is a known flaw but fixing it does not
unblock LIVE-GREEN — capture still requires QEMU to be alive.

### Guest serial log (verbatim after run)

Same as Round-11, including `desktop-ready` (line 25 of 34) followed by
FAULT + shortcut:fail + TEST FAILED. No regression; the kernel is doing
the same thing Round-11 observed.

## What changed in this round

### `test/system/simpleos_desktop_framebuffer_spec.spl`

1. Added `_build_once(target)` helper that reuses the existing build
   artifact when present. The first `it{}` still calls `build_os`
   unconditionally (hard gate for build regression); the second `it{}`
   now calls `_build_once` which returns true if
   `file_exists(target.output)` is already true.
2. Raised `wait_for_serial_marker` timeout 60_000 → 180_000 ms.
3. Updated the marker-not-seen branch comment to cite Round-12 and name
   the OS-side blocker (early QEMU exit after desktop-ready), so future
   rounds don't waste another round investigating harness.

No OS, runtime, or compiler code edited. Both existing `it{}` structural
invariants preserved.

## Why LIVE-GREEN still fails

Two orthogonal issues, only one of which is a harness bug:

1. **Harness false negative (known race, fix deferred):**
   `wait_for_serial_marker`'s inner early-exit uses a pre-flush
   `serial_output` value captured at the top of the loop iteration.
   Touching the harness would affect every QMP spec; leaving the
   fix to a dedicated harness round is lower risk.

2. **OS-side early exit (true LIVE-GREEN blocker, out of scope):**
   After `[desktop-e2e] desktop-ready` the entry fn
   `desktop_e2e_main()` invokes `launcher_shortcut_dispatch(KEY_B,
   META_MODIFIER)` which hits a no-NVMe FAULT chain, returns false,
   causes `desktop_e2e_main()` to return false, which exits with
   `TEST FAILED` via isa-debug-exit. Until the shortcut path is either
   made tolerant of no-NVMe (fall back to local-fallback manifest the
   way Browser Demo's local path does) or the entry keeps QEMU alive
   for a screendump grace period (e.g. spin-sleep N seconds between
   desktop-ready and shortcut dispatch), LIVE-GREEN is unreachable.

## Proposed next round (Round-13)

Pick exactly one of these two tracks:

**Track A — OS-side fix (preferred):**
Insert a paint-settle phase in `desktop_e2e_entry.spl` between the
`desktop-ready` marker and `launcher_shortcut_dispatch`. Minimum
viable: emit `desktop-ready`, busy-wait ~2 seconds (enough for the
harness's 100 ms poll + QMP screendump round-trip + PPM write), THEN
attempt the shortcut dispatch. On no-NVMe the shortcut path still
FAULTs but QEMU now stays alive for the capture. Guarded behind an
env-var check (`SIMPLE_DESKTOP_E2E_CAPTURE_GRACE_MS`) so the
serial-only lane is not slowed.

Territory: `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`.
Out of scope for Round-12 by guardrail; explicitly in scope for a
round that allows OS edits.

**Track B — harness flush-race fix (standalone):**
Update `wait_for_serial_marker` in
`test/qemu/os/common/qemu_os_harness.spl` to re-read the serial log
one more time (after a small settle) before returning false on the
process-dead branch. Low risk if the re-read is limited to the
early-exit path. Unblocks the `with_apps` spec too.

Do both and LIVE-GREEN lands in a single round.

## Gate decision

- SYS-GUI-006 **LIVE-GREEN:** not achieved. Spec + doc changes in this
  round are a net improvement (1× build, 47% faster failure, precise
  diagnosis) but do not satisfy the PPM-compare acceptance criterion.
- SYS-GUI-008 Row 4 **dependency** on SYS-GUI-006 LIVE-GREEN:
  **still blocked**. Row 4 status in
  `doc/03_plan/gui_drawing_layer_variations.md` remains "Round-0 plan
  landed 2026-04-14 · Round-1 gated on sys-gui-006 Round-11 LIVE-GREEN"
  — the reference to Round-11 should be superseded by Round-13 once
  Track A or Track B lands.

> **Round-13 update (2026-04-14):** Track A (paint-settle) landed and
> the harness race is cleared (see
> `sys_gui_006_round13_status_2026-04-14.md`). LIVE-GREEN remains
> blocked, now on a different root cause: `qmp_send` calls
> `shell(cmd)` with the wrong import resolution — Round-14 will fix
> the `qmp_client.spl` path and unblock the capture.
