# SYS-GUI-006 Bare Desktop Framebuffer Baseline — Resume Checklist

**Status (Agent η, Round 8, 2026-04-14):** NOT LIVE-PROVEN. Blocked on
TWO upstream regressions, not one. The Round-7 single-bug story was
optimistic — γ's parser fix alone is insufficient, and the live lane
that used to reach `desktop-ready` regressed.

> **Round-10 update (2026-04-14):** Blocker 1 below is now **CLEARED** by
> commit `e516e2a0f484 fix(interpreter): add GLOBAL_ENUMS fallback for
> cross-module enum variant lookup`. Verified by re-running the spec
> from `/home/ormastes/dev/pub/simple` — zero `method \`X86_64\` not found`
> errors, kernel build `it{}` passes (`phase=native-build OK`,
> ~33s elapsed). Blocker 2 (`launcher:fail registered=0` before
> `desktop-ready`) remains active; it gates the live-lane `it{}` via the
> `wait_for_serial_marker(..., "[desktop-e2e] desktop-ready", 60000)` in
> the spec. See
> `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md` for
> evidence and Blocker 2 handoff instructions.
>
> **Round-11 update (2026-04-14):** Blocker 2 is now **CLEARED** in the
> kernel image. Commit `f940 fix(codegen): qualify MIR method calls via
> MirLocal type when receiver.ty is unnamed` correctly routes
> `shell.init()` to `DesktopShell.init`. Live QEMU serial log
> (`build/os/simpleos_desktop_qemu_serial.log`) now emits every expected
> marker: `[shell] init: wm service initialized`,
> `[launcher] Initializing app launcher...`,
> `[launcher] Registered 4 default apps`,
> `[desktop-e2e] launcher-ready apps=4`, and
> `[desktop-e2e] desktop-ready`. **However**, the spec still fails
> because the harness-side `wait_for_serial_marker` races against
> sequential `build_os` calls that burn ~51 s of the 60 s budget before
> QEMU even spawns. Not an OS/compiler regression — a spec/harness
> issue. See `sys_gui_006_round11_status_2026-04-14.md` for full
> evidence and Round-12 remediation plan.
>
> **Round-13 update (2026-04-14):** Harness race **CLEARED** by pairing a
> 2,000 ms pre-sleep in the spec with an OS-side `_paint_settle()` in
> `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`. Instrumented
> run confirms `wait_for_serial_marker returned saw_ready=true` on the
> first iteration. **New blocker surfaced**: `capture_qemu_vm` aborts
> on `qmp_send → shell(cmd)` — `std.io` does not export a `shell`
> function so the name resolves to the `shell` class (static-only),
> and the interpreter raises
> `semantic: too many arguments for class \`shell\` constructor`.
> See `sys_gui_006_round13_status_2026-04-14.md` for full evidence
> and Round-14 remediation plan (fix `qmp_send` in
> `src/lib/nogc_sync_mut/qemu/qmp_client.spl` to use `shell.run(...)`
> or a direct `rt_process_run` extern).

## One-command retry

Once both blockers below are cleared, a single command records and
self-validates the baseline:

```bash
UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter \
  && bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter
```

The first invocation records `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`.
The second runs self-compare under `profile_wm_default` at `>=95%`.
Both must pass without editing the spec, the baseline, or the tolerance
profile. A third fresh-record compared against the committed baseline
must also exceed 95% — otherwise the capture is non-deterministic and
must be investigated (masking the unstable region via tolerance profile
or freezing the clock/cursor at boot), NOT masked by lowering the gate.

## Blocker 1 — Interpreter `std.spec` load chain still broken  [CLEARED 2026-04-14, Round-10]

> **Round-10 status:** CLEARED by commit `e516e2a0f484`. The fix added a
> `GLOBAL_ENUMS` fallback in the interpreter's enum variant lookup
> (`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:428`,
> `src/compiler_rust/compiler/src/interpreter_call/mod.rs:302,454,676`,
> populated from `interpreter_call/block_execution.rs:595-596,1069-1070`)
> so cross-module enum references resolve even when the defining
> module is loaded out of order. The historical analysis below is
> retained for archival reference.

**Territory:** Agent γ / Z2 (`src/compiler_rust/**`)

**What Round-7 thought was the whole bug:** `pub enum` after an
`@allow(...)` attribute crashed the interpreter parser at
`src/compiler_rust/lib/std/src/core/json.spl:5-7`.

**What's actually on current main (verified by η):** γ's parser fix
IS already applied in the working copy at
`src/compiler_rust/parser/src/parser_impl/items.rs` —
`parse_pub_item_with_attrs` now accepts `TokenKind::Enum` and
`TokenKind::Union` after attributes. The `Failed to parse module
.../core/json.spl` error is gone from
`UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`.

**But the semantic cascade is still there.** Interpreter mode now
emits ~60 "Export statement references undefined symbol" WARNs from
`std.spec`, `std.spec.matchers`, and `std.spec.config`
(`global_runtime`, `set_example_state`, `ExampleState`, `Runtime`,
`be_true`, `BeTrueMatcher`, `ExecutionMode`, `ModeSet`,
`ProjectConfig`, `parse_toml_test_config`,
`discover_project_config`, …). The spec body then fails at
`build_os(target)` with:

```
✗ builds desktop_e2e_entry.spl into a baremetal kernel
    semantic: method `X86_64` not found on type `Architecture`
✗ boots desktop, captures framebuffer via QMP, and matches baseline
    semantic: method `X86_64` not found on type `Architecture`
```

Same verbatim error the Round-7 README documented. Verified twice —
once with `bin/simple` symlinked to `target/bootstrap/simple` (the
shipping 28 MB binary), once with the freshly cargo-built 49 MB
`target/release/simple`. Both contain γ's parser fix, both
reproduce the cascade, so the remaining bug is NOT in the parser.

**Hypothesis:** a second site in the interpreter module loader also
rejects `pub enum` / `pub union` constructs (perhaps further up the
import chain — `std.spec.matchers`, `std.spec.config`,
`std.common.image.ppm_decode` all import `std.core.json` transitively
and each defines their own `pub enum`), or the cascade has a
second independent root. Either way, once `--mode interpreter` loads
`std.spec.*` without "Export statement references undefined symbol"
warnings, step 3 of the recording procedure should produce a real
PPM.

**Alternative fix:** make `--mode native` actually execute `it{}`
bodies via the cranelift backend. `bin/simple os test
--scenario=x64-desktop-test` already parses the exact same type
graph through the native path without issue, proving the bug is
interpreter-local.

**Sibling repro:** `test/system/engine2d_in_qemu_spec.spl` under
`bin/simple test --mode interpreter` fails identically. Any fix that
unblocks us also unblocks SYS-ENGINE2D.

## Blocker 2 — Live lane regression: `launcher:fail` before `desktop-ready` [CLEARED 2026-04-14, Round-11]

> **Round-11 status:** CLEARED by compiler commit `f940 fix(codegen):
> qualify MIR method calls via MirLocal type when receiver.ty is
> unnamed`. Live serial log now contains `[desktop-e2e] desktop-ready`
> along with all prerequisite shell/launcher markers. The Blocker 2
> diagnostic in `launcher_module_storage_fix_plan_2026-04-14.md`
> correctly identified `(A) Method-dispatch mis-selection` as the
> root cause. Historical analysis below retained for archive.

**Territory:** Agent α / δ (`src/os/**`, `examples/simple_os/**`)

**Verified by η on 2026-04-14 03:40 UTC:**

```
$ bin/simple os test --scenario=x64-desktop-test
...
[desktop-e2e] spl_start
[desktop-e2e] boot
[vfs-init] Starting storage stack initialization...
[vfs-init] PCI cache ready (from C boot)
[vfs-init] No NVMe device found -- VFS unavailable
[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs
[GUI] fb_addr=0x0x00000000fd000000 fb_w=0x0000000000000400
[shell] new: creating minimal session (no builder DSL)...
[shell] new: WmService created
[desktop-e2e] shell-ready
[desktop-e2e] launcher:fail registered=0
TEST FAILED
```

The lane now stops at `[desktop-e2e] launcher:fail registered=0`
and never emits `[desktop-e2e] desktop-ready`. Round-7 README said
Agent V's compositor fix reached `desktop-ready` live — a later
commit regressed that path.

**Implication for SYS-GUI-006:** even if blocker 1 lands and the
interpreter runs the spec body, `wait_for_serial_marker(handle,
"[desktop-e2e] desktop-ready", 60000)` will time out at 60 s and
the spec will hard-fail (by design — do NOT soften the gate). Both
blockers must clear before the baseline can be captured.

**Probable regression site:** the launcher / app_manifest wiring in
`src/os/desktop/shell.spl` or `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl`
— `registered=0` indicates no apps were registered with the
launcher before the registration assertion fired. Agent α/δ should
check the `app_manifest::register_default_apps` call site and the
launcher builder invocation between `shell-ready` and `desktop-ready`.

## What Agent η left ready on main

- `test/system/simpleos_desktop_framebuffer_spec.spl` — unchanged;
  trigger marker is `[desktop-e2e] desktop-ready`, profile is
  `profile_wm_default`, baseline path is
  `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`.
  Already hard-fails on marker miss (correct — regression gate).
  Already self-heals on first UPDATE_BASELINE=1 run. No spec edits
  required once blockers clear.
- `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm` —
  still the zero-byte placeholder. Do NOT commit a fake or
  synthetic PPM; the gate exists specifically to catch that.
- `test/baselines/simpleos_desktop_framebuffer/README.md` — Round-8
  status appended below Round-7 status with dual-blocker breakdown.
- QEMU 8.2.2 + `-vga std` pre-verified available on this host.
- `src/compiler_rust/parser/src/parser_impl/items.rs` — γ's
  uncommitted parser fix observed in working copy. Left as-is
  (η does not own that tree). γ must commit it as part of the
  blocker-1 fix.

## Remaining blocker (Round-11) — harness marker-wait race

**Territory:** test harness (`test/system/simpleos_desktop_framebuffer_spec.spl` plus
`_wait_for_serial_marker` under `src/lib/.../qemu_runner.spl`).

The spec currently calls `build_os(target)` twice (once per `it{}`), each
taking ~24–28 s, before `spawn_guest_with_qmp` runs. Total wall time is
~52 s, leaving < 2 s of the 60 s `wait_for_serial_marker` budget to run
against a QEMU that has only just started booting. Serial log on disk
confirms `desktop-ready` is emitted, but after the spec has already
given up.

**Remediation (Round-12):** collapse duplicate `build_os` call, or lift
it to a shared before-all step, or raise the wait budget. Any one fix
is sufficient.

> **Round-12 update (2026-04-14):** Duplicate `build_os` collapsed via
> `_build_once(target)` helper + wait budget raised to 180 s. Wall-clock
> dropped from 52 s → 28 s (verified). **BUT** the race was not the
> whole story — direct QEMU timing shows the guest is alive only
> ~250–300 ms after emitting `desktop-ready` before `isa-debug-exit`
> fires (kernel FAULTs in the downstream `launcher_shortcut_dispatch`
> path on no-NVMe and returns false → `TEST FAILED`). LIVE-GREEN via
> QMP screendump is therefore blocked on an OS-side fix, not harness.
> See `sys_gui_006_round12_status_2026-04-14.md` Track A / Track B for
> the proposed Round-13 plans. Row 4 of
> `doc/03_plan/gui_drawing_layer_variations.md` remains gated on a
> future round that lands LIVE-GREEN.

## Verification sequence once the harness race is resolved

1. `bin/simple os test --scenario=x64-desktop-test` — must emit
   `[desktop-e2e] desktop-ready` on the serial log (proves
   blocker 2 is cleared — **already verified 2026-04-14 Round-11**).
2. `bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
   — must execute `it{}` bodies without the "Export statement
   references undefined symbol" cascade (proves blocker 1 is
   cleared). Will fail the second `it` on missing baseline until
   step 3.
3. `UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
   — captures the PPM, writes it to the baseline path, passes.
   Eyeball the PPM (wallpaper + dock + shell chrome, no apps,
   no panic stripes, no tearing). Expected dimensions: 1024x768
   per `bga_init_framebuffer` in `desktop_e2e_entry.spl`.
4. `bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl --mode interpreter`
   — self-compare at `>=95%` under `profile_wm_default`. PASS.
5. Third fresh recording compared against the committed baseline —
   also `>=95%`. PROVE DETERMINISM, not just self-identity.
6. `jj commit -m "test(sys-gui-006): refresh desktop framebuffer baseline"`
   with the PPM plus whichever README updates reflect reality.
7. SYS-GUI-006 LIVE-PROVEN — close the gate in
   `doc/03_plan/simpleos_small_complete_gui_status_2026-04-13.md`.
