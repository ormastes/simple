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

## Added Repo Artifacts

- `config/t32/trace32_x11_container.Dockerfile`
- `config/t32/trace32_x11_container.compose.yml`
- `config/t32/trace32_x11_container.shs`

## Proposed Bring-Up Flow

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
