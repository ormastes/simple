# TRACE32 X11 Container Recovery Plan

**Date:** 2026-03-12

## Goal

Bring TRACE32 up in a reproducible Linux environment that does not depend on
the host X server state, then expose the Remote API on port `20000` for the
repo's remote interpreter and `t32rem` smoke checks.

This plan is specifically for the failure mode seen on this host:

- `t32rem localhost port=20000 PING` returns `error initializing TRACE32`
- direct `t32marm` launches fail or die before a usable session appears
- `xvfb-run` on the host is not sufficient by itself

## What The Container Can Fix

- provide a clean X11 runtime via in-container `Xvfb`
- provide the non-Qt X11 and font libraries used by `t32marm`
- remove dependence on stale host `/tmp/.X*-lock` state
- provide a repeatable launch entrypoint for CI or local recovery

## What The Container Cannot Fix

- a broken or incomplete TRACE32 vendor install under `/opt/t32`
- missing USB device access for the Lauterbach probe
- udev/permission issues on the host
- missing TRACE32 screen/plugin files in the vendor package itself

The container helps only if the mounted `/opt/t32` install is otherwise valid
for `t32marm` and the probe nodes are reachable.

## Root Cause: 2013-era T32 Binary

The installed `/opt/t32/bin/pc_linux64/t32marm` binary dates from **2013-07-23**.
This is a 13-year-old build linked against X11/Xt (Motif-era toolkit), which
crashes with `XtCreatePopupShell requires non-NULL parent` under modern Xvfb.

Key observations:

- `t32marm` (non-Qt) links against `libXt.so.6`, `libXmu.so.6`, `libXp.so.6` —
  classic X Toolkit Intrinsics. The `XtCreatePopupShell` crash happens because
  the 2013-era Xt initialization does not handle modern X server behavior.
- `t32marm-qt` (Qt variant) **does exist** at the same path but requires
  `libQtGui.so.4` and `libQtCore.so.4` (Qt 4), which are not available on the
  host. Qt 4 was EOL in 2015.
- `t32screenqt5.so` is missing from the install, confirming no Qt 5 screen
  plugin is available either.
- The 2013 build predates `SCREEN=OFF` support. Only `SCREEN=INVISIBLE` is
  available, and it still requires a functional X display.

A modern TRACE32 install (2020+) would likely resolve all of these issues, but
upgrading requires a Lauterbach maintenance agreement.

## Added Repo Artifacts

- `config/t32/trace32_x11_container.Dockerfile`
- `config/t32/trace32_x11_container.compose.yml`
- `config/t32/trace32_x11_container.shs`
- `config/t32/t32_rcl_only.t32` — minimal RCL-only config (no PBI section)

## Proposed Bring-Up Flow

### Phase 0. Try RCL-only config (no PBI) to isolate X11 vs probe issues

Before building the container, test whether `t32marm` can even reach the RCL
bind stage without the USB probe. This separates two failure modes:

- **X11/Xt startup crash** — happens before any probe communication
- **PBI/USB failure** — happens after successful GUI init

Use the minimal config at `config/t32/t32_rcl_only.t32`:

```bash
xvfb-run -a /opt/t32/bin/pc_linux64/t32marm -c config/t32/t32_rcl_only.t32
```

This config has no `PBI=` section, so TRACE32 should skip probe detection.

Expected outcomes:

- If it **still crashes** with `XtCreatePopupShell` → the X11/Xt layer is the
  blocker, not USB. The 2013 binary cannot handle modern Xvfb.
- If it **starts and binds port 20000** → the probe section was causing the
  crash. Re-add `PBI=USB` and debug that layer.
- If it **starts but does not bind** → RCL/NETASSIST config is not reaching the
  network layer. Check `ss -ulnp | grep 20000`.

After this test, `t32rem localhost port=20000 PING` should be attempted to
verify whether the RCL listener is actually functional.

### Phase 1. Build the container image

Use:

```bash
config/t32/trace32_x11_container.shs build
```

This builds a small Ubuntu-based image with:

- `xvfb`
- `xauth`
- `x11-utils`
- the X11/font libraries needed by the non-Qt `t32marm`

### Phase 2. Launch TRACE32 in the container

Use:

```bash
config/t32/trace32_x11_container.shs up
```

The compose service:

- mounts the repo at `/workspace`
- mounts `/opt/t32` read-only from the host
- mounts `/dev/lauterbach` and `/dev/bus/usb`
- starts `t32marm` under `xvfb-run`
- publishes port `20000`

### Phase 2b. Try t32marm-qt variant

If the non-Qt `t32marm` cannot get past the Xt initialization crash, try the
Qt variant instead. It exists at `/opt/t32/bin/pc_linux64/t32marm-qt`.

The Qt variant requires `libQtGui.so.4` and `libQtCore.so.4` (Qt 4). These are
not available on the current host or in the current container image.

To test:

1. Install Qt 4 compatibility libraries in the container:

```dockerfile
RUN apt-get install -y libqt4-gui || true
```

Or on Ubuntu 24.04+ where Qt 4 packages are removed, download the `.so` files
from an older Ubuntu release and place them where `ld` can find them.

2. Update the entrypoint to prefer `t32marm-qt`:

```bash
/opt/t32/bin/pc_linux64/t32marm-qt -c config/t32/t32_stm_headless.t32
```

The existing `config/t32/trace32_entrypoint.shs` already has fallback logic
that tries `t32marm` first and falls back to `t32marm-qt`.

Qt 4's rendering pipeline is more tolerant of virtual framebuffers than raw
Xt/Motif, so this variant may survive under Xvfb where the non-Qt binary
crashes.

### Phase 3. Verify Remote API readiness

Use:

```bash
config/t32/trace32_x11_container.shs ping
```

Expected success:

- `t32rem localhost port=20000 PING` returns success

If this still fails, the remaining problem is not X11/container isolation. The
next checks are:

1. verify `/opt/t32/bin/pc_linux64/t32marm` starts inside the container
2. verify the mounted `/opt/t32` install includes the required runtime pieces
3. verify the Lauterbach USB device is visible and usable in the container

## Acceptance Criteria

The container recovery is considered successful when all of the following hold:

- `config/t32/trace32_x11_container.shs up` leaves a live TRACE32 session
- `config/t32/trace32_x11_container.shs ping` succeeds
- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
  reports TRACE32 status as `ready`

## Current Result On This Host

The plan is implemented in-repo, but not yet fully validated end-to-end here.

Observed local behavior before the container path:

- host `xvfb-run` still left `t32rem ... PING` failing with
  `error initializing TRACE32`
- `t32marm` did not stay alive long enough to expose the Remote API

That means the X11 cleanup alone was not enough on the host. The next useful
validation is the new containerized launch path, because it separates X11
runtime issues from the remaining TRACE32 install/probe issues.
