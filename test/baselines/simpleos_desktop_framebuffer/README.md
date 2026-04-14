# SimpleOS Desktop Framebuffer Baseline (SYS-GUI-006)

This directory holds the checked-in baseline PPM for
`test/system/simpleos_desktop_framebuffer_spec.spl` — the visual
regression lane for the SimpleOS "Small Complete GUI" milestone.

## Files

- `desktop_scene.ppm` — golden baseline captured via QMP screendump
  on a clean `x64-desktop-test` guest run. On a fresh checkout this
  may be a zero-byte placeholder (see below).

## Current status (Agent Z3 / Round 7, 2026-04-13)

The committed `desktop_scene.ppm` is still a **zero-byte placeholder**.

**SYS-GUI-006 is NOT yet LIVE-PROVEN.** Round-7 progress vs Round-5:

- Agent V's compositor fix landed: `bin/simple os test
  --scenario=x64-desktop-test` now reaches `[desktop-e2e]
  desktop-ready` live. The serial lane after `desktop-ready`
  still fails downstream at `[desktop-e2e] shortcut:fail`
  (Agent Z1's domain), but that is not on the bare-desktop
  baseline path — the spec only waits on `desktop-ready`.

- Agent X's `bin/simple` swap: the test runner's `interpreter`
  mode now actually executes `it` block bodies (the spec body
  reaches `build_os(target)` and yields a real semantic error,
  whereas Round-5 saw a sub-20-ms no-op PASS). `--mode native`
  and `--mode smf` still print "Native mode for tests not
  supported, using safe mode" and fall back to static analysis,
  so interpreter is the only mode that can run the body.

The remaining blocker preventing baseline capture is now a
single upstream bug in interpreter parsing:

**Interpreter parser cannot handle `pub enum` after an `@allow(...)`
attribute.** The `std.spec` import chain transitively loads
`src/compiler_rust/lib/std/src/core/json.spl`, which begins:

```
@allow(primitive_api, bare_bool)

pub enum JsonValue:
    ...
```

Interpreter module loader fails this file with:

```
ERROR ... module_loader: 504: Failed to parse module
  path=".../core/json.spl"
  error=Unexpected token: expected fn, struct, class, mixin,
  or mod after pub with attributes, found Enum
```

The cascading effect is that `std.spec`, `screenshot`, and the
shared OS type graph load with missing exports (`ExampleState`,
`Runtime`, `parse_toml_test_config`, `discover_project_config`,
…). When the spec body then calls `build_os(target)` against a
target whose `arch` field is `Architecture.X86_64`, the type
system has been corrupted enough that it prints:

```
✗ builds desktop_e2e_entry.spl into a baremetal kernel
    semantic: method `X86_64` not found on type `Architecture`
✗ boots desktop, captures framebuffer via QMP, and matches baseline
    semantic: method `X86_64` not found on type `Architecture`
```

even though `Architecture` (defined in
`src/os/kernel/arch/arch_context.spl`) clearly has the
`X86_64` variant and the same call works fine through
`bin/simple os test --scenario=x64-desktop-test` (which uses
the native compiler path, not the interpreter loader). The
sibling spec `test/system/engine2d_in_qemu_spec.spl`
reproduces the exact same error verbatim under `bin/simple
test --force-rebuild`, confirming this is global to the
interpreter / `std.spec` load path and not spec-local.

Fix lives in `src/compiler_rust/**` (Agent Z2's territory) —
either teach the interpreter parser to accept `pub enum` after
attribute prefixes, or have the test runner's `--mode native`
path actually execute `it` bodies via the cranelift backend
(which already parses `json.spl` correctly — `bin/simple os
test --scenario=x64-desktop-test` proves this). Once either
half lands, `UPDATE_BASELINE=1 bin/simple test
test/system/simpleos_desktop_framebuffer_spec.spl` records the
real baseline without any further edit here.

The "with apps" variant
(`test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`)
is still tagged `@tag:pending_until_shortcut_fix` and skips
cleanly while Agent Z1 stabilises the shortcut/launcher chain.

## Recording procedure

1. Make sure the desktop integration lane reaches at least
   `[desktop-e2e] desktop-ready`:

   ```
   bin/simple os test --scenario=x64-desktop-test
   ```

   The scenario's serial log must contain `[desktop-e2e] desktop-ready`
   before the bare-desktop baseline can be meaningfully recorded.
   (The downstream `shortcut:ok` / `remote-grouping:ok` markers are
   only required for the "with apps" variant in
   `test/system/simpleos_desktop_with_apps_framebuffer_spec.spl`.)

2. Ensure the test runner can load `std.spec` cleanly under
   `--mode interpreter` (or, equivalently, that `--mode native`
   stops falling back to safe-mode for `it` block execution).
   On current main, interpreter mode runs `it` bodies but the
   `std.spec` → `screenshot` → `std.core.json` import chain
   trips an interpreter-parser bug on `pub enum` after `@allow`,
   which propagates as `semantic: method X86_64 not found on
   type Architecture` from `build_os(target)`. Until this is
   fixed (see "Current status" above), step 3 fails in ~300 ms
   without ever spawning QEMU.

3. Run the framebuffer spec once with `UPDATE_BASELINE=1`:

   ```
   UPDATE_BASELINE=1 bin/simple test test/system/simpleos_desktop_framebuffer_spec.spl
   ```

   The spec will boot the desktop kernel under QEMU, wait for the
   `[desktop-e2e] desktop-ready` serial marker (bare-desktop paint
   proxy), call `capture_qemu_vm` via QMP screendump, and write
   the resulting frame here as `desktop_scene.ppm`.

4. **Eyeball the PPM.** Open it and verify:

   - desktop wallpaper / background is present
   - dock or taskbar is drawn in the expected place
   - no panic stripes, no tearing, no obviously uninitialised regions
   - app windows are NOT yet present (this is the bare-desktop
     capture; the with-apps variant handles that case)

   If any of the above look wrong, do NOT commit. Fix the underlying
   desktop render path first.

5. Re-run without `UPDATE_BASELINE=1` to confirm self-compare passes
   at `>=95%` under `profile_wm_default`. Run it a second time from
   a fresh recording to verify determinism. If two fresh recordings
   do not match at `>=95%`, the capture is non-deterministic on this
   scenario — narrow the tolerance profile or mask the non-stable
   region (typical culprits: clock widget, cursor position, any
   animated keyframe).

6. Commit the updated baseline with an intentional message:

   ```
   jj commit -m "test(sys-gui-006): refresh desktop framebuffer baseline"
   ```

## Tolerance profile

The spec compares against this baseline with `profile_wm_default`
from `src/os/compositor/tolerance_profile.spl`. Whole-scene gate:
`>=95%` match (9500 on the 0-10000 scale). Per-region thresholds
(solid 99.90%, text 95.00%, blur 93.00%, gradient 98.00%,
decoration 97.00%) enforce stricter limits on chrome panels than
on font-AA and glass-blur regions.

## Dimensions

Expected framebuffer dimensions are governed by `desktop_e2e_entry`
(`bga_init_framebuffer(1024, 768, 32)` at time of writing). If that
entry changes resolution, delete `desktop_scene.ppm` and re-record.
