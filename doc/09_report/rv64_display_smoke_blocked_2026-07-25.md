# RV64 Display-Smoke QMP Evidence

- contract_version: 2
- status: fail
- reason: build-failed
- elf: build/os/simpleos_riscv64_display_smoke.elf
- serial_log: (not produced — QEMU never launched)
- scanout_ppm: (not produced)
- scanout_raw: (not produced)
- ready: 0
- lifecycle_markers: 0
- width: 0
- height: 0
- stride: 0
- present_revision: 0
- scanout_address: 0
- scanout_bpp: 0
- scanout_format:
- scanout_generation: 0
- scanout_scene_revision: 0
- scanout_capture_size: 0
- scanout_capture_origin: qemu-pmemsave
- nonblack: 0
- canonical_palette_witnesses: 0
- canonical_palette_names:
- wm_font_input_mode: 0
- wm_font_input_contract_version: 1

## Verdict

BLOCKED (not a display/rendering FAIL — the ELF was never produced, so QEMU
was never launched and no QMP scanout capture was attempted). This is
distinct from a genuine `missing-elf` probe result: the earlier probe never
even tried to build; this run tried to build 3 times and root-caused why the
build phase itself cannot complete in this environment.

## What changed since the earlier "missing-elf" run

The prior probe (doc/09_report/rv64_display_smoke_qmp_evidence_*.md lineage)
never invoked `bin/simple os build --scenario=riscv64-display-smoke` at all
— the ELF file was simply absent. This run **did** invoke the build 3 times
(the session's build-attempt cap) and got past the earlier "mtools missing"
symptom, but hit a second, deeper blocker in the same media-provisioning
phase. The ELF (kernel binary) itself was never reached because
`bin/simple os build --scenario=riscv64-display-smoke` fails during the
**disk-media phase** (`ensure_riscv64_desktop_disk_image`), before the
kernel/ELF compile step runs.

## Root cause (two layered defects, both in the FAT32-media verification path)

1. **Environment gap (worked around, not a code bug):** `mtools`
   (`mtype`/`mdir`) is not installed via apt on this host (`dpkg -l | grep
   mtools` → not installed; `apt-cache policy mtools` shows only a candidate,
   no installed version) and there is no repo-managed unprivileged fallback
   invoked automatically. A previously-built local mtools exists at
   `/tmp/simple-mtools/root/usr/bin/{mtype,mdir,...}` (leftover from an
   earlier session/build). I symlinked those binaries into
   `~/.local/bin` (already on default `$PATH`, no sudo needed, no repo files
   touched) so `command -v mtype` / `command -v mdir` now succeed for any
   subprocess spawned by `bin/simple`.

2. **Real code defect (the actual blocker, NOT fixed — scope is probe/build,
   not editing production gate logic without authorization):**
   `_desktop_disk_image_has_required_fonts()` in
   `src/os/_QemuRunner/scenario_exec.spl` (around line 288-306) verifies each
   extracted font file is non-empty with the idiom:
   ```
   mtype -i "{img_path}" ::/SYS/FONTS/{font_name} 2>/dev/null | test -s /dev/stdin
   ```
   run under `/bin/sh -c "..."`. On this host `/bin/sh` is `dash`
   (`readlink -f /bin/sh` → `/usr/bin/dash`). `test -s /dev/stdin` stats a
   pipe's `st_size`, which is always reported as 0 for a FIFO/pipe under
   POSIX — so `test -s` on a piped `/dev/stdin` **always evaluates false**,
   regardless of how much data actually flowed through the pipe. This is
   independently reproducible outside the Simple runtime:
   ```
   $ /bin/sh -c 'mtype -i img ::/SYS/FONTS/NSANSSC 2>/dev/null | test -s /dev/stdin; echo rc=$?'
   rc=1
   ```
   even though `mtype -i img ::/SYS/FONTS/NSANSSC` on its own produces
   17,772,300 bytes of real font data (verified by hand: `mtype ... | wc -c`
   → 17772300). So `_desktop_disk_image_has_required_fonts()` reports
   "incomplete" for **every** correctly-populated riscv64 desktop disk image
   on any dash-based `/bin/sh` (stock on Ubuntu/Debian), which is why
   `ensure_riscv64_desktop_disk_image()` prints
   `[ensure_riscv64_desktop_disk_image] desktop font projection is
   incomplete` and `bin/simple os build --scenario=riscv64-display-smoke`
   fails at `phase=media` every time — confirmed 3/3 attempts, identical
   failure, despite the on-disk image (`build/os/fat32-riscv64-desktop.img`,
   134,217,728 bytes) manually verified to contain all 16 required font
   files plus `NOTICES.MD`, and correctly lacking `::/SYS/APPS` and
   `::/SIMPLE.ELF` (the fs-exec-payload rejection checks also pass).

   I did **not** patch `scenario_exec.spl` — that changes gate logic outside
   this lane's authorized scope (build ELF + run probe) and the task
   explicitly forbids weakening gates; a `test -s /dev/stdin`-in-a-pipe fix
   is arguably a correctness fix rather than a weakening, but it's still a
   change to shared production verification code that deserves its own
   reviewed change, not a drive-by inside a probe-evidence task.

## Bug to file

`_desktop_disk_image_has_required_fonts()` /
`_desktop_disk_image_has_required_manifests()`-style checks in
`src/os/_QemuRunner/scenario_exec.spl` use `<cmd> | test -s /dev/stdin` to
test "did this piped command produce output" — broken under dash (stock
Ubuntu `/bin/sh`) because pipe `stat()` reports size 0. Same idiom should be
audited across scenario_exec.spl / scenario_disks.spl. Suggested fix
direction: replace with `[ -n "$(cmd)" ]` or check exit status +
byte-count via a temp file, not `test -s /dev/stdin` after a pipe.

## Attempts (3/3, cap reached)

1. `bin/simple os build --scenario=riscv64-display-smoke` (no PATH change) —
   failed at `phase=media`, "desktop font projection is incomplete"
   (mtools missing from PATH at that point).
2. Same command with `mtools` PATH-exported in the same shell — failed
   identically (env inheritance confirmed fine via a `process_run_timeout`
   probe script, so PATH was not actually the residual blocker for this
   attempt — the dash `test -s /dev/stdin` defect was already present
   underneath).
3. Same command with mtools symlinked persistently into `~/.local/bin` —
   failed identically. Root-caused per above; STOPPING per the 3-attempt
   cap rather than patching production verification logic.

## What is/isn't evidence

- `build/os/fat32-riscv64-desktop.img` — present, 134,217,728 bytes, manually
  verified complete (all 16 fonts + NOTICES.MD present; SYS/APPS and
  SIMPLE.ELF correctly absent).
- `build/os/simpleos_riscv64_display_smoke.elf` — still absent. No QEMU
  session was ever started. No serial log, no QMP scanout, no
  width/height/stride/nonblack/palette evidence exists for this run — this
  report does **not** claim any scanout numbers, real or zero-as-pass.
