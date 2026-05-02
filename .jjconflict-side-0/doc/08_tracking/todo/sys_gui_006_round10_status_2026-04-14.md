# SYS-GUI-006 — Round 10 Status (2026-04-14)

**Agent:** Round-10 verification (post-`e516` compiler blocker clearance)
**Workspace:** `/tmp/simple-round15` (jj, branched off `main@origin`)
**Binary used:** `/home/ormastes/dev/pub/simple/bin/simple` → `src/compiler_rust/target/bootstrap/simple`
**Verification spec:** `test/system/simpleos_desktop_framebuffer_spec.spl` (bare-desktop lane)

## TL;DR

- **Blocker 1 (compiler, `Architecture.X86_64` semantic cascade): CLEARED** by
  commit `e516e2a0f484 fix(interpreter): add GLOBAL_ENUMS fallback for
  cross-module enum variant lookup` (landed on `main@origin`).
- **Blocker 2 (OS, `launcher:fail registered=0` before `desktop-ready`):
  STILL ACTIVE.** The live-lane QMP capture `it{}` times out at 60s
  waiting for a `desktop-ready` marker that is never emitted because
  `desktop_e2e_entry.spl:108-115` guards the marker behind
  `launcher_get_app_count() > 0`.
- **Bare-desktop lane cannot LIVE-GREEN on Blocker 1 alone.** There is
  no no-apps fallback path in `desktop_e2e_entry.spl` — `launcher:fail`
  is a hard return, not a warning. SYS-GUI-006 bare remains blocked
  externally on an OS-scoped fix.

## Evidence of Blocker 1 clearance

Ran from the main-repo cwd (`/home/ormastes/dev/pub/simple`, fresh cache invalidated):

```
bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter
```

Key observations from the full run (log saved to `/tmp/sys_gui_006_round10_full.log`):

- **Zero occurrences of `method \`X86_64\` not found on type \`Architecture\`**
  (`grep -c` = 0). Previously ~2 occurrences per run.
- `build_os(target)` succeeds:
  `[build][x86_64] phase=native-build OK elapsed_ms=32859`
- First `it{}` **passes** for the first time since Round-7:
  `✓ builds desktop_e2e_entry.spl into a baremetal kernel`
- `std.spec.*` export warnings ("Export statement references undefined
  symbol") still emit at module-load time but no longer cause a hard
  semantic failure downstream — they are harmless noise the interpreter
  loader recovers from.
- Remaining failure is isolated to the live-lane QMP boot `it{}`:
  `✗ boots desktop, captures framebuffer via QMP, and matches baseline`
  with `timeout: execution exceeded 0 second limit` after ~66s, which is
  the 60s `wait_for_serial_marker` on `[desktop-e2e] desktop-ready`.

Test summary: `2 examples, 1 failure` — exactly the transition from the
Round-9 triage expectation ("3 examples, 2 failures" with semantic cascade)
to the predicted post-Blocker-1 state ("2 examples, 1 failure" with
live-lane marker timeout).

## Evidence of Blocker 2 active

`launcher_get_app_count()` is the direct gate. Trace in
`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`:

```
val registered = launcher_get_app_count()           # line 108
if registered == 0:
    serial_println("[desktop-e2e] launcher:fail registered={registered}")  # line 110
    return                                                                  # no desktop-ready emitted
...
serial_println("[desktop-e2e] desktop-ready")       # line 115 (never reached)
```

`wait_for_serial_marker(..., "[desktop-e2e] desktop-ready", 60000)` in the
spec therefore times out. Round-9 verified this exact sequence on the
live lane independently.

## What the OS-side agent needs to do (Blocker 2 handoff)

**Territory:** `src/os/desktop/shell.spl`, `src/os/services/launcher/**`,
`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`.
**Owner lineage:** Agent α or δ.

### Investigation steps

1. Add a single-line trace before `launcher_init()` in
   `DesktopShell.init()` (`src/os/desktop/shell.spl:258-261`):
   `serial_println("[shell] pre-launcher-init manifests_dir_exists={...}")`
   and a matching line after: `serial_println("[shell] post-launcher-init count={launcher_get_app_count()}")`.
2. Rebuild with `bin/simple native-build … desktop_e2e_entry.spl …` and
   rerun `bin/simple os test --scenario=x64-desktop-test`.
3. Two branches:
   - If `post-launcher-init count=0` and `load_app_manifests()` in
     `src/os/desktop/shell.spl:718` returned 0 manifests → the manifest
     directory is missing or empty in the boot image. Wire the 4
     built-in apps (`launcher.spl` lists them) into the manifest loader
     fallback path.
   - If `load_app_manifests()` returned N>0 but
     `launcher_get_app_count()==0` → baremetal module-level array
     storage bug (the one blamed in the with-apps checklist as
     "Agent alpha territory"). Fix the global array visibility across
     the `load_app_manifests → launcher_register` boundary.

### Minimum acceptable output

`bin/simple os test --scenario=x64-desktop-test` serial log must emit
`[desktop-e2e] desktop-ready` within 60 s of boot. Anything short of
that keeps SYS-GUI-006 bare-desktop gated.

## Can the bare-desktop lane LIVE-GREEN without Blocker 2?

**No, not under the current spec contract.**

- `desktop_e2e_entry.spl:110` hard-returns on `registered==0`. No
  fallback path emits `desktop-ready`.
- The spec's `wait_for_serial_marker(..., "[desktop-e2e] desktop-ready", 60000)`
  is the only success condition; dropping it or relaxing the wait
  would be a green-washed pass, which Round-9 triage and the bare-desktop
  resume checklist both explicitly forbid.

A scope-change would be theoretically possible (separate a
"shell-ready only" lane from the "launcher-ready" lane), but that is
outside Round-10's remit and would need to be negotiated as a
sys-gui-006 ticket modification, not a Round-10 verification pass decision.

## Files this round did NOT change

- No compiler, OS, or runtime code touched (doc-only round).
- Working copy edits visible under `/home/ormastes/dev/pub/simple` at
  session start (listed in the Round-0 harness status) are unrelated
  to this round and were not staged or committed here.
- No baseline PPM was captured (second `it{}` still blocked on marker).

## Next round pre-conditions

Round-11 can declare SYS-GUI-006 bare-desktop LIVE-GREEN iff:

1. An OS-scoped agent lands a Blocker 2 fix and a verified run of
   `bin/simple os test --scenario=x64-desktop-test` emits
   `[desktop-e2e] desktop-ready`.
2. `UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
   captures a real PPM (wallpaper + dock + shell chrome, no apps,
   1024x768) at `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`.
3. Two fresh recordings each compare >=95% to the committed baseline
   under `profile_wm_default`.

The Round-8 verification sequence in the bare-desktop resume checklist
still applies verbatim once Blocker 2 lands.
