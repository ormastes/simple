# Baremetal WM present owner v1

## Gap

The x86-64, AArch64, and RISC-V64 desktop entries render through the shared WM
scene, but their readiness markers correlate output differently. RISC-V has a
platform display generation, AArch64 has a RAMFB checksum/frame counter, and
x86 publishes its boot scanout generation. There was no common owner that
prevented a stale frame, replayed platform generation, or changed scanout from
being promoted as the latest successful WM output.

## Boundary

`BaremetalWmPresentOwnerV1` is the sole mutable owner of the last admitted
presentation tuple. Architecture adapters retain MMIO, firmware, framebuffer,
and present-call ownership. They pass only bounded scalar identity and receipt
data after their platform operation returns. The owner stores no framebuffer
pointer and performs no allocation proportional to frame size.

Canonical class fields remain file-private. Cross-file callers receive only
the immutable receipt snapshot and scalar read-only accessors; mutation routes
exclusively through `commit_present`.

The immutable scanout identity binds architecture, boot scanout identifier,
dimensions, stride, and pixel width. The identifier is an opaque adapter-owned
scanout handle; it is neither an address nor dereference authority. V1 accepts the three production
64-bit architecture codes, BGRA-compatible 32-bit pixels, exact packed stride,
and dimensions no larger than 16384 in either axis.

## Commit rules

A commit requires the exact boot identity, a successful platform-present bit,
a positive scene revision, and positive frame/output generations. Scene
revision may remain equal for a refresh, but may not move backward. Frame IDs
must advance strictly. Output generation is a lifecycle epoch: it may stay
equal (as on x86 boot scanout) but may not move backward. Rejection updates only the bounded
diagnostic reason; it never advances canonical presentation state.

This makes readiness correlation O(1) in time and space and adds no pixel copy.

## Architecture entry wiring

The x86-64, AArch64, and RISC-V64 production desktop entries now construct one
boot-scoped owner from metadata already admitted by their platform adapter.
x86 uses the positive BGA scanout generation as its opaque boot identity;
AArch64 and RISC-V64 use the value `1` for their platform-owned singleton
primary output. These values are handles only. Framebuffer addresses remain in
the architecture entry and are never passed to or retained by the owner.

Readiness is emitted only after the first owner commit. AArch64 first requires
successful RAMFB configuration plus its existing bounded visual-commit result.
RISC-V64 commits only after `riscv64_display_present` succeeds and the display
capsule publishes a positive generation; every later changed frame advances a
local frame id and is admitted before its input/frame marker. AArch64 likewise
admits each first/changed frame after the platform visual-commit result. x86's
existing interactive loop and markers are unchanged; its first rendered frame
is admitted before the pre-existing readiness markers, while subsequent loop
presentation remains owned by `DesktopShell` and retains its existing behavior.

All added admission work is fixed-field O(1), performs no frame-sized copy or
allocation, and does not add dispatch to the idle input path.
