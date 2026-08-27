# SimpleOS bare Engine2D QEMU-user fill matrix — 2026-08-12

## Verdict

**PASS for the declared cross-ISA exact-fill user-mode matrix; no 8K/80
claim.** The earlier ARM64 and x86 link-admission failures documented below
were repaired. A fresh authoritative run on 2026-08-12 completed with exit 0
for x86-64/SSE2 host-user, AArch64/NEON QEMU-user, and RV64GCV/RVV QEMU-user.

## Harness and scope

Canonical harness:

```sh
timeout 120 bash scripts/check/check-simpleos-gui-fill-qemu-user-matrix.shs
```

It builds and executes the production bare framebuffer stubs plus exact-pixel
probes for:

| ISA | execution | claimed by the harness |
| --- | --- | --- |
| x86_64 | host user mode | SSE2 `rt_gui_fill4` exact pixels and SIMD receipts |
| ARM64 | `qemu-aarch64` user mode | NEON `rt_gui_fill4` exact pixels and SIMD receipts |
| RV64 | `qemu-riscv64` user mode | RVV `rt_gui_fill4` exact pixels and SIMD receipts |

This is deliberately narrower than a SimpleOS QEMU boot: it does not boot a
guest, present scanout, measure full-frame throughput, exercise blend/copy
operations, or establish 8K at 80 FPS.

## 2026-08-12 execution record

An initial invocation using `sh` exited immediately with status 2:

```text
scripts/check/check-simpleos-gui-fill-qemu-user-matrix.shs: 4: set: Illegal option -o pipefail
```

That is a launcher mismatch, not a kernel result: the script declares Bash.

A single bounded declared-interpreter attempt was then run in a dedicated
process group and captured to
`/tmp/simpleos-gui-fill-qemu-receipt.EUdtED/matrix.stdout-stderr`:

```text
command: setsid timeout --signal=TERM --kill-after=10s 120s bash scripts/check/check-simpleos-gui-fill-qemu-user-matrix.shs
controller_pid=1892971
controller_pgid=1892971
exit_status=1
ld.lld: error: undefined symbol: g_fb_h
>>> referenced by simpleos_gui_fill_live_probe.c
>>> did you mean: g_fb_w
>>> defined in: .../arm-runtime.o
```

The receipt is terminal and reliable: it is a **link-admission failure**, not
a QEMU-user failure. ARM64 probe execution never began; because the matrix is
fail-fast, x86_64 and RV64 were not reached in this attempt. This document
makes no SIMD-kernel, bare-boot, display, throughput, or 8K/80 assertion.

## Relationship to the booted render lane

The booted desktop evidence gate remains
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`. Its latest retained
evidence is [the 2026-08-07 QEMU report](simpleos_2d_render_qemu_evidence_2026-08-07.md),
which was blocked before QEMU boot by the freestanding-link admission gate.
Neither that report nor this user-mode probe provides a live bare display,
blend-span, full-frame, or 8K/80 measurement.

## Next evidence step

The ARM64 `g_fb_h` ABI defect was repaired in the production bare runtime and
the next bounded matrix run reached a real QEMU-user receipt:

```text
simpleos_bare_gui_fill_arm64=pass isa=neon execution=qemu-user
```

That run then stopped at the separate x86 link admission gaps
`g_fb_h` and `rt_gui_simd_fill_scalar_parity`; x86 and RV64 are therefore not
yet promoted. The ARM64 result is an exact-pixel fill probe only, not a booted
desktop/display/blend/full-frame/8K measurement. Repair the x86 ABI, rerun the
full bounded matrix, then use a separate OVMF/QEMU desktop run before adding
operation-level timings or an 8K/80 budget row.

The x86 ABI was subsequently repaired and the focused optimized host-user
probe passed with exact pixels and enabled/hit/chunk/tail/scalar-parity
receipts. Its original O2 failure was the raw ELF probe entry's stack
alignment, not the SSE2 fill kernel. Scalar comparison is compiled only under
`SIMPLEOS_GUI_FILL_PROBE`, leaving the production SIMD hot loop without a
second per-vector walk. The full matrix was deliberately not run again after
that source change, so RV64 and matrix-wide PASS remain pending.

The RV64 bare ABI was then implemented with clipped dynamic-VL RVV stores and
probe-only scalar parity. Its first post-fix compile exposed literal `\\n`
text in the inline-assembly string; after correcting the instruction
separators, the one bounded canonical RV64 run passed:

```text
simpleos_rv64_gui_fill_qemu_user=pass isa=rvv vlen=128
simpleos_rv64_gui_fill_pixels=exact sentinels=unchanged
simpleos_rv64_gui_fill_receipts=enabled,hit,chunks,tail,scalar-parity
```

Together with the ARM64 QEMU-user and x86 optimized host-user focused receipts,
all three ISA fill kernels now have individual exactness evidence. A fresh
combined matrix run is still required for its own matrix-wide PASS, and none
of these user-mode kernel probes establishes booted scanout, blending/copy
coverage, frame timing, or 8K/80 throughput.

## Combined matrix receipt

A fresh bounded matrix run completed with exit status 0:

```text
simpleos_bare_gui_fill_arm64=pass isa=neon execution=qemu-user
simpleos_bare_gui_fill_x86_64=pass isa=sse2 execution=host-user
simpleos_rv64_gui_fill_qemu_user=pass isa=rvv vlen=128
simpleos_rv64_gui_fill_pixels=exact sentinels=unchanged
simpleos_rv64_gui_fill_receipts=enabled,hit,chunks,tail,scalar-parity
simpleos_gui_fill_qemu_user_matrix=pass pixels=exact parity=true
```

This closes the matrix's exact-fill kernel gate for its declared three ISA
rows. It remains user-mode kernel evidence only: no SimpleOS guest boot,
physical scanout, blend/copy operation matrix, full-frame frame time, or 8K/80
claim follows from this result.

## Current-state refresh

The combined matrix was rerun from the current shared worktree after the
retained-frame and SIMD span work. It again exited 0 with the same six terminal
receipt lines shown above. This refresh supersedes the historical FAIL verdict
at the top of the document while preserving the failure chronology for audit.
