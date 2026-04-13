# SimpleOS Small Complete GUI — Agent Task Breakdown

## Goal

Parallelize the work needed to close the first `x86_64` QEMU-backed SimpleOS GUI OS milestone.

## Agent 1 — Desktop integration lane

Own:

- real desktop entry selection
- `x64-desktop-test` scenario alignment
- serial-marker-based desktop integration coverage

Deliver:

- one authoritative desktop integration path
- one serial-only regression lane with actionable logs

## Agent 2 — App ownership and lifecycle

Own:

- `Hello World` single-window path
- `Browser Demo` multi-window path
- graceful exit, terminate, and crash cleanup validation

Deliver:

- stable launcher-owned `app_id` across launcher, shell, WM, and compositor
- live lifecycle assertions

## Agent 3 — GUI framebuffer verification

Own:

- QMP framebuffer capture integration
- desktop baseline recording and compare
- tolerance profile selection for the desktop capture

Deliver:

- one desktop QEMU spec with screendump and baseline compare
- baseline artifact and update procedure

## Agent 4 — Storage-backed follow-up

Own:

- disk-image boot path
- desktop boot with storage enabled
- one storage-backed app-launch smoke

Deliver:

- next-milestone proof that the desktop path still works on the intended persistent environment
