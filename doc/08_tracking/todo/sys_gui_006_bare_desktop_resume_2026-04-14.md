# SYS-GUI-006 Bare Desktop Framebuffer Baseline — Resume Checklist

**Status (Agent η, Round 8, 2026-04-14):** NOT LIVE-PROVEN. Blocked on
TWO upstream regressions, not one. The Round-7 single-bug story was
optimistic — γ's parser fix alone is insufficient, and the live lane
that used to reach `desktop-ready` regressed.

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

## Blocker 1 — Interpreter `std.spec` load chain still broken

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

## Blocker 2 — Live lane regression: `launcher:fail` before `desktop-ready`

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

## Verification sequence once both blockers land

1. `bin/simple os test --scenario=x64-desktop-test` — must emit
   `[desktop-e2e] desktop-ready` on the serial log (proves
   blocker 2 is cleared).
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
