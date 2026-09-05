# TRACE32 Docker Experiment

**Date:** 2026-03-08

## Goal

Use a privileged Docker container to bypass the host's missing
`/dev/lauterbach/trace32/*` device path and test whether TRACE32 can be brought
up there for `t32_native` / `t32_gdb` smoke execution.

## Added Repo Helpers

- `scripts/t32_docker/Dockerfile`
- `scripts/t32_docker/run_t32_container.sh`

These helpers create a small Ubuntu 24.04 runtime with `xvfb` and mount:

- `/opt/t32`
- `/dev/bus/usb`
- host X11 runtime libraries

## What Worked

Inside a privileged container, after creating:

```text
/dev/lauterbach/trace32/3-3 -> /dev/bus/usb/003/003
```

`t32usbchecker` reached the Lauterbach probe and reported:

```text
Basic communication...CONNECT request OK
USB communication OK
```

That confirms the container workaround can satisfy TRACE32's device-path
expectation.

## What Still Failed

Launching real PowerView still failed.

Without X:

```text
Error: Can't open display:
```

With `Xvfb`:

```text
Error: XtCreatePopupShell requires non-NULL parent
```

`t32rem localhost port=20000 PING` therefore still reports:

```text
error initializing TRACE32
```

## Conclusion

The Docker workaround proves the USB-path issue is real and partially
workaroundable, but it is still not enough to achieve a stable hidden TRACE32
PowerView session for automated `t32_native` / `t32_gdb` execution.

The remaining blocker is now specifically the Linux TRACE32 front-end runtime in
this environment, not the repo-side test runner or spec code.
