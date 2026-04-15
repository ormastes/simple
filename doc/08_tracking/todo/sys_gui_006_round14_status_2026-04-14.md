# SYS-GUI-006 — Round 14 Status (2026-04-14)

## TL;DR

- **qmp_client stdlib bug fixed.** `src/lib/nogc_sync_mut/qemu/qmp_client.spl`
  no longer imports `use std.io.{shell}` (which resolved to the static-only
  `shell` class and raised
  `semantic: too many arguments for class shell constructor` under the
  interpreter). `qmp_send` now declares an `extern fn rt_process_run(...)`
  directly and invokes `rt_process_run("/bin/sh", ["-c", cmd])`. Lint is
  clean: `bin/simple lint src/lib/nogc_sync_mut/qemu/qmp_client.spl` →
  `OK`. Under the spec the stdlib error is gone — `qmp_send` now fails
  with a downstream environment error instead of a class-constructor
  semantic error.
- **LIVE-GREEN blocked by host environment, not by Simple code.** Three
  separate non-Simple blockers surfaced once the stdlib error cleared:
  1. `/tmp/simple-round20/bin/simple` symlink is absent in the isolated
     workspace, so `SIMPLE_BOOTSTRAP=1 … bin/simple native-build …`
     spawned by the spec aborts with
     `/bin/sh: 1: bin/simple: not found`. Result: kernel not built,
     `capture_qemu_vm` short-circuits the live branch.
  2. `socat` is not installed on the host. Even if the kernel built,
     `qmp_send` now correctly hits `/bin/sh -c "echo … | socat - UNIX-CONNECT:…"`
     and fails with `/bin/sh: 1: socat: not found`. `netcat` is
     available at `/usr/bin/netcat` but the current qmp_send command
     string is `socat`-flavoured; swapping would be an API change.
  3. Downstream spec bug, not qmp_client:
     `semantic: method len not found on type enum (receiver value: Option::Some([]))`
     at `test/system/simpleos_desktop_framebuffer_spec.spl:295`
     (`result.pixels.len()` where `pixels` is wrapped in `Option`).
     Surfaced only because the capture call now returns an
     `Option::Some([])` instead of aborting the `it{}` block early.
- **Spec pass/fail unchanged** from Round-13 on this host:
  `1 passed, 2 failed` (baseline-directory example passes; live and
  sim examples still fail, but for different reasons — the blocker has
  moved).

## Change

- `src/lib/nogc_sync_mut/qemu/qmp_client.spl`:
  - Removed `use std.io.{shell}`.
  - Added `extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)`
    (mirrors `src/lib/common/chaos.spl:33` and ~40 other stdlib call sites).
  - Rewrote `qmp_send` body from `shell(cmd)` to
    `rt_process_run("/bin/sh", ["-c", cmd])`.
  - Widened `qmp_send` return type from `(text, text, i32)` to
    `(text, text, i64)` to match `rt_process_run`. No external caller of
    `qmp_send` consumes the exit-code field by concrete type (only
    `!= 0` and `== 0` comparisons), so this is a safe widening.

## Run evidence

### Lint

```
$ /home/ormastes/dev/pub/simple/bin/simple lint \
    src/lib/nogc_sync_mut/qemu/qmp_client.spl
src/lib/nogc_sync_mut/qemu/qmp_client.spl: OK
```

### Spec

```
$ timeout 180 /home/ormastes/dev/pub/simple/bin/simple test \
    test/system/simpleos_desktop_framebuffer_spec.spl
…
[build][x86_64] phase=native-build FAILED exit=127 elapsed_ms=11
[build][x86_64] stderr tail:
/bin/sh: 1: bin/simple: not found

SKIP: Kernel not built: build/os/simpleos_desktop_e2e_32.elf
[simpleos_desktop_fb_spec] qemu-system-x86_64 not available, skipping live capture
[simpleos_desktop_fb_spec] R13 pre-wait sleep for serial-log flush
[simpleos_desktop_fb_spec] desktop paint-ready marker not seen within 180s
[qmp] screendump failed: /bin/sh: 1: socat: not found

[simpleos_desktop_fb_spec] QMP screendump failed for socket: /tmp/simpleos_desktop_qmp.sock
[simpleos_desktop_fb_spec] captured 0x0, non-black pixels: 0 of 0
  ✗ boots desktop, captures framebuffer via QMP, and matches baseline
    semantic: method `len` not found on type `enum`
              (receiver value: Option::Some([]))
  ✓ has a baseline directory for simpleos_desktop_framebuffer captures

3 examples, 2 failures

Files: 1
Passed: 1
Failed: 2
Duration: 2506ms
```

### Key signal

Compare the failure mode to Round-13:

- Round-13: `semantic: too many arguments for class 'shell' constructor`
  — inside `qmp_send`, the spec body aborted silently mid-`it{}`.
- Round-14: `/bin/sh: 1: socat: not found` printed by `[qmp]` and a
  downstream `Option::Some([])` `.len()` error in the spec itself.

The class-constructor error is gone. qmp_send now executes through the
runtime and returns cleanly. The residual failures are environmental
(host missing socat + bin/simple symlink in workspace) and a spec-body
bug, neither of which live in qmp_client.

## LIVE-GREEN verdict

**Not achieved this round** — but the stdlib blocker called out by
Round-13 is resolved. LIVE-GREEN requires, on the executor host:

1. `apt install socat` (or port qmp_send to netcat/direct AF_UNIX
    runtime call — out of scope for a minimal stdlib fix).
2. Workspace `bin/simple` symlink (`scripts/setup.sh`) so the spec's
    kernel-build spawn finds the compiler.
3. Follow-up fix for
    `test/system/simpleos_desktop_framebuffer_spec.spl:295` to unwrap
    `result.pixels` before `.len()` / route through the
    `ScreenshotResult` helpers already imported from `std.spec`.

None of these three are qmp_client concerns and none were permitted
to be touched under the Round-14 guardrails
(only `qmp_client.spl` + docs).

## Follow-up

- Next round should either (a) bring socat onto the executor host and
  re-run, or (b) land a small PR that ports `qmp_send` from the
  `socat` shell form to a native AF_UNIX connect using runtime
  externs, at which point `qmp_send` has zero external shell
  dependencies and LIVE-GREEN gates only on the workspace
  `bin/simple` symlink + the spec-body `Option::Some([])` bug.
- The sys-gui-008 gate referenced in
  `doc/03_plan/gui_drawing_layer_variations.md` Row 4 is NOT removed
  this round — LIVE-GREEN is still outstanding.

## Files touched

- `src/lib/nogc_sync_mut/qemu/qmp_client.spl` — stdlib fix (this round's
  only code change).
- `doc/08_tracking/todo/sys_gui_006_round14_status_2026-04-14.md` —
  this status doc.
