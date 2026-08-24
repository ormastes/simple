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
The next integration slice should construct one owner per desktop boot and
require its accepted receipt before emitting each architecture's readiness or
input-to-frame correlation marker. Until that wiring lands, this module is a
prerequisite contract and not runtime proof that all three entries use it.
