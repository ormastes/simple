# FreeBSD QEMU cleanup resolves the wrong root and lacks live-guest checks

Status: open; discovered during the requested RISC-V FreeBSD VM preparation.

Owner: RISC-V FreeBSD bootstrap lane, targeting `release_phase3`.

## Evidence

`scripts/qemu/cleanup-qemu-temp.shs` defines its root using the script
directory followed by `/..`. For this location the result is `scripts/`,
so `VM_DIR` becomes `scripts/build/freebsd/vm`, rather than the repository's
`build/freebsd/vm`. This is a path-resolution defect, independently of whether
the intended directory currently exists.

The same script removes the PID file, serial log and all overlay images
without first checking whether the recorded QEMU process is alive or whether
the overlay belongs to another active run. Its cleanup scope is therefore
unsuitable for the requested regular disk maintenance. It was inspected but
was not executed.

## Required repair and verification

Resolve the repository root from `scripts/qemu/../..`. Resolve and validate
absolute cleanup targets before removing anything. Preserve admitted base
images, live guest overlays, current logs and unrelated run artifacts. Require
run ownership and a terminal process state before deleting a run's disposable
files; a PID file alone is not sufficient evidence of either state.

Verify an isolated fixture with a retained base, a disposable completed-run
overlay, a live-run overlay, and an unrelated sibling directory. Only the
owned completed-run disposable files may be removed. Include a negative test
for an invalid or escaping root and stale/reused PID metadata.

Do not execute this script as the host disk-cleanup remedy until repaired.
