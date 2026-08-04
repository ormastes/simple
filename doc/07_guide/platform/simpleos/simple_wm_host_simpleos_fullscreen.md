# Production Simple WM Host and SimpleOS Fullscreen

## Scope

This lane converges the production hosted WM and SimpleOS desktop on shared internal-window, top-lane, taskbar, Simple Web content, and Simple 2D rendering contracts.

Host display fullscreen and internal-window maximize are different operations:

- `F11` requests native borderless fullscreen for the host surface.
- The internal titlebar maximize control changes only the selected Simple window.
- SimpleOS always owns the full detected framebuffer; maximize/restore applies to internal windows only.

## Production Paths

| Surface | Authority | Projection | Renderer |
|---|---|---|---|
| Host | `HostCompositor.windows` | revisioned `SharedWmScene` | shared Draw IR chrome/taskbar + Simple Web `WmContentFrame` + host backend |
| SimpleOS | `DesktopShell.compositor` / `WmService` | `runtime_scene_snapshot()` | shared Draw IR chrome/taskbar + Engine2D framebuffer backend |

`SharedWmScene` is immutable projection data, not a second mutable WM. `WmContentFrame` values must match the authoritative scene/window/content revisions, dimensions, origin, pixel count, and checksum. Invalid frames fail closed.

## Host Transition Contract

The host surface tracks `Windowed` or `BorderlessFullscreen` plus `Requested`, `AwaitingResize`, `Applied`, or `Failed` transition phase. Each request has a positive nonce and deadline. Resize and scale acknowledgements may arrive in either order; stale nonces are rejected. Denial, timeout, or close rolls back without changing internal-window state.

Windowed outer x/y/w/h and scale are retained through the typed Winit facade. Fullscreen exit restores the saved outer position after the matching physical acknowledgement.

## Shared Objects

The rich executor renders exactly one authoritative taskbar. Pinned, running, tray, and clock objects come from `TaskbarModel`; the executor reserves right-side tray/clock space and clips excess running objects rather than overlapping them. A target without a pinned registry must supply an empty pinned list instead of treating processes as pinned launchers.

Host content uses content-only Simple Web requests: the outer WM owns the titlebar, so content artifacts must not contain a second `.wm-app-titlebar`. Content revisions remain stable until title/body/size/scroll changes.

## SimpleOS Fake-Path Removal

The production `DesktopShell.run_baremetal` loop renders `runtime_scene_snapshot()`, `runtime_taskbar_model()`, and validated content-only Simple Web frames through the shared backend. It no longer calls `_draw_baremetal_overlay`, and a failed app launch creates no overlay-only window. Compatibility rendering remains isolated to legacy/demo APIs and is not a production entrypoint or completion evidence.

The production x86_64 entry launches process-owned Browser Demo, Hello World, and Clang surfaces from payloads present in the canonical FAT32 fixture, validates dynamic scanout metadata, and keeps one persistent framebuffer Engine2D. Set-1 F11 and PS/2 AUX pointer packets share one guest-owned monotonic input sequence. `DesktopShell` correlates each accepted event with its IRQ marker, resulting WM state, and rendered frame marker; QMP submission alone is not evidence.

### Font path

SimpleOS rootfs, initramfs, and pure-Simple nested FAT32 builders validate and
stage all 16 pinned selected candidates under readable registry-owned VFAT long
names in `/SYS/FONTS`, with unique 8.3 compatibility aliases. The guest treats
each path only as a byte source and registers the canonical `/assets/fonts/...`
identity. Pure-Simple FAT32 readers
use a bounded 32 MiB ceiling, above the largest selected face; the C
compatibility reader remains bounded at 4 MiB. The WM
does not own a font renderer: its scene
carries Draw IR family/identity semantics and the persistent Engine2D owns
`FontRenderer` materialization. Missing guest file support, an identity mismatch,
or an unavailable vector runtime retains the fixed bitmap fallback.
Registered-only source paths now shape the pinned Hindi and Arabic/Urdu
witnesses from validated VFS bytes without the host font ABI, then materialize
them through the existing selected-byte `FontRenderer`. This is executable
regression coverage, not retained guest/QEMU framebuffer evidence; the Browser
frame and pixel-oracle gates still fail until that evidence is captured.
VFAT writing and lookup currently support ASCII long names; nested directories
chain across clusters, while invalid names and fixed-root overflow fail closed.

Packaging alone is not a font-rendering PASS. The canonical x86_64 desktop
reads the pinned face from the deterministic guest path
`/SYS/FONTS/NOTOSANS`, validates exactly 1,708,408 bytes with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`,
and emits its font marker only after hashing the live taskbar-clock MMIO crop.
The `Capture SimpleOS pinned-font pixels` scenario must record that guest
path/length/hash, WM Draw IR identity, guest marker, and independently hashed
dynamic-scanout QEMU `pmemsave` crop. Host rendering, serial-only markers,
repository file presence, and synthetic pixels are blockers, not substitutes.

## Scenario Manuals

- `doc/06_spec/03_system/os/wm/simple_wm_host_fullscreen_spec.md`
- `doc/06_spec/03_system/os/wm/simpleos_wm_fullscreen_spec.md`
- `doc/06_spec/03_system/os/wm/simple_wm_performance_spec.md`

The production QEMU evidence wrapper is
`sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`. It must report
correlated keyboard and pointer input, authority revision, backend, font crop,
and framebuffer evidence. Source inspection, demo markers, Rust-seed execution,
fixed QEMU metadata, or unverified screenshots cannot satisfy the scenarios.

For the LLVM 23.1 browser lane, first build and admit the signed current
toolchain provider (`llvmorg-23.1.0-rc2`; stable 23.1.0 is not published as of
2026-08-04). Bootstrap then admits the compiler providers in order: Stage 2
may produce Stage 3, the provenance-admitted Stage 3 may produce Stage 4, and
only the current-source Stage 4 full CLI may launch this production wrapper.
Stage 2, Stage 3, the Rust seed, and `build/native_probe/simple` are not
launchable substitutes. The native probe is diagnostic-only even when its
native smoke passes.

Build the full-stage provider first, preserving the Stage 2/3 caches when a
bounded retry is needed:

```sh
SIMPLE_NO_STUB_FALLBACK=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload --full-cli --no-mcp
```

The qualifying executable is
`build/bootstrap/full/<triple>/simple`, accompanied by the verified sibling
`simple.provenance.env` and the Stage 4 essential-tools smoke receipt. See the
[bounded Clang 23.1 bootstrap and QEMU workflow](../../app/llm/clang_23_1_bootstrap_browser_qemu_workflow.md)
for the stage admission rules and recovery cap. Then launch the canonical
wrapper with the exact admitted Stage 4 path and coherent LLVM tools:

```sh
export LLVM_23_1_PREFIX="$PWD/build/toolchains/llvm-23.1.0-rc2"
export SIMPLE_LLVM_PREFIX="$LLVM_23_1_PREFIX"
SIMPLE_BIN="$PWD/build/bootstrap/full/<triple>/simple" \
SIMPLE_BIN_SOURCE=full-stage4-provenance \
SIMPLEOS_WM_NATIVE_BACKEND=llvm \
CLANG="$LLVM_23_1_PREFIX/bin/clang" \
SIMPLE_CLANG="$LLVM_23_1_PREFIX/bin/clang" \
LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
SIMPLE_LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
BUILD_DIR="$PWD/build/evidence/clang-23.1-browser-qemu" \
REPORT_PATH="$PWD/doc/09_report/clang_23_1_browser_qemu_evidence.md" \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Replace `<triple>` with the directory produced by the same bootstrap run; do
not copy a similarly named binary from another worktree. The wrapper rechecks
the sibling Stage 4 provenance against the current source tree before it builds
or boots anything. This guide does not claim a current live QEMU PASS: retain
the wrapper report and evidence bundle, and report the exact failure when the
bounded lane has not converged.

The browser builder writes
`build/os/apps/browser_demo/clang-23.1-evidence.txt`; it records the compiler,
linker, archiver, versions, and hashes beside the produced browser ELF. The
wrapper must prove that those exact ELF bytes were staged as
`/SYS/APPS/BROWSMF.SMF` before framebuffer or input receipts can pass. Inside
the guest, the filesystem toolchain is launched as `/usr/bin/clang-23.1`, with
`/usr/bin/clang` as its compatibility alias. The LLVM-18-only Rust
`inkwell`/`llvm-sys` binding is a declared bootstrap blocker, never an accepted
provider for this QEMU lane.

For the hosted CSS-override parity lane, run
`sh scripts/check/check-wm-host-css-override-evidence.shs`. It writes a stable
six-token glass fixture and executes the canonical production host launcher for
both default and override states. A pass requires the hosted override receipt,
a changed effective material identity with the package source identity retained,
and different presented-buffer pixels. Its FIFO commands are explicitly
diagnostic synthetic compositor input, not Winit or physical interaction
evidence.

## Current Verification Limits

The 2026-07-24 focused live attempt used
`bin/release/x86_64-unknown-linux-gnu/simple` (SHA-256
`a3302eeaabe9e050117a0778806b9fc354409010e293ec3402bd097ee4534fa2`).
Its native build remained CPU-bound for about 13 minutes, exceeded the
requested `--timeout 300`, emitted an empty build log, and was terminated
without refreshing the kernel. The wrapper therefore reported
`wm-simple-web-build-failed`; QEMU did not launch and no crop was promoted.
The wrapper now uses the canonical WM target's unoptimized profile under a
900-second host watchdog, retains its native cache after timeout, and admits
only an ELF64 little-endian x86_64/SHA-256-validated candidate with matching
wrapper, compiler, profile, and source-content provenance. It rechecks the
source revision before promotion, so concurrent edits fail rather than
admitting a mixed-source ELF. Explicit kernel overrides must identify
`e_machine=62`; explicit images must have the canonical SimpleOS FAT32
BPB/header and pass the installed host FAT checker. Both remain labeled
external. A generated default disk is labeled `built-from-admitted-kernel`
only for a current-source build/cache hit, or
`built-from-external-elf-validated` when built from an explicit validated ELF.
The next live run remains blocked in the isolated x86 worktree because its only
pure-Simple executable exits 139; do not substitute a Rust seed or an unrelated
artifact. Source contracts are supporting evidence only.

Scalar safety includes enum payloads: raw PMM allocation owns the bitmap path
instead of wrapping `PageFrame?`, and VMM table allocation consumes the raw
physical address. The direct QEMU target uses
`arch_x86_64_direct_boot_init()` because its multiboot wrapper supplies scalar
memory bounds, not valid Limine request/optional aggregates. Generic Limine
early initialization remains unchanged for actual Limine boot lanes.

Direct serial phase markers prove architecture setup, hardware-MMIO selection,
PMM initialization, and VMM table construction return before CR3 activation.
VMM's operational PML4 and HHDM values are scalar-owned; compatibility
aggregates are snapshots only. Pre-activation evidence records the scalar root
and the PML4[0], PDPT[0], and PD[0] entries so an invalid page-table chain
cannot be mistaken for a fullscreen or framebuffer failure.

The pure-Simple VMM uses explicit raw CR3 runtime primitives; legacy tagged
`RuntimeValue` helpers must not decode native `u64` roots. The production QEMU
target attaches the canonical x86_64 FAT32 image as an NVMe device because its
process-owned Browser Demo, Hello World, and Clang launches are real filesystem
executables. Missing media fails before launch rather than falling through to
filesystem faults or synthetic windows. Framebuffer construction likewise
uses scalar scanout fields rather than passing `FramebufferInfo` by value.
Evidence aborts with `guest-serial-fault-storm` when serial output exceeds 1
MiB, preventing recovered-fault loops from making marker scans unbounded.

The direct FAT32 boot verifier crosses no tagged text boundary for its fixed
version probe. It compares numeric 8.3 directory bytes for `VERSION.TXT`,
`SYS`, and `NVFSVER.TXT`, then reads the real cluster through the pure-Simple
NVMe DMA path. This is a deterministic disk lookup, not a hardcoded success:
missing directory entries or failed cluster transfers still fail readiness.

Direct FAT scratch ownership is scalar (`cpu_addr`, `phys_addr`, `byte_len`).
The module-global `SharedDmaBuffer` is compatibility state only; production
directory traversal never calls methods or reads fields through that aggregate.
A local DMA descriptor is assembled only at the NVMe submission boundary.

Live numeric FAT traversal has resolved the real Browser Demo and Hello World
payloads. The canonical image does not contain the former Shell or Editor
payload assumptions, so production now requires `BROWSMF.SMF`, `HELLOSMF.SMF`,
and `CLANGSMF.SMF`. The registry cache and launcher names match those exact
files; a missing payload remains a readiness failure. Framebuffer Engine2D,
mouse bounds, compositor dimensions, and evidence logging use the validated
scanout width, height, and stride scalars rather than reading the stage3-corrupt
`FramebufferDriver` aggregate fields.

The production compositor is constructed through the explicit backend
contract: `Compositor.with_backends` receives the persistent framebuffer
Engine2D adapter, a concrete PS/2 `InputBackend`, and validated scalar screen
dimensions. It must not call the unowned legacy `Compositor.new(fb, keyboard,
mouse)` shape. Baremetal shell initialization uses the canonical launcher
registry already populated from the FAT payload cache and does not perform the
hosted manifest scan.

Initial x86_64 desktop processes enter through the installed Simple syscall
13 bridge with numeric app IDs. The bridge adopts the returned scheduler into
the trap runtime, so process ownership cannot be represented by a fabricated
PID. Boot executable bytes for Browser Demo, Hello World, and Clang use a
numeric loader cache populated only after their real FAT cluster reads; this
avoids stage3-corrupt `AppEntry` aggregate traversal while preserving the
filesystem payload as the process-image source of truth.

Host evidence also fails closed on incomplete self-hosted builds. Any skipped
module, nonzero failed-file count, or generated unresolved stub removes the
candidate artifact and reports `production-native-build-incomplete`; a linked
file alone is not executable provenance.

The recovered compiler crash was traced to direct array-return values losing
their resolved type during bootstrap constructor lowering. Source now preserves
the declared Array/Slice return and registers its runtime materialization, with
concrete and generic constructor regressions. A fresh canonical compiler deploy
and QEMU pixel run are still required; source repair is not guest evidence.

The current stage3 freestanding compiler also emits entry-module scalar values
as weak zero-return text stubs and ignores the requested x86-64-v1 CPU baseline.
The production entry therefore keeps early hardware operands local, and the
QEMU target declares `qemu64,+bmi2` to match the emitted `shlx` instruction.
Both compiler divergences have tracking bugs and must be removed when stage3
preserves entry data and CPU baseline selection. The QEMU fixture currently
uses the `max` CPU model because `qemu64,+bmi2` still raised `#UD` on `shlx`.

SimpleOS activates the VMM page table after building its identity map; BAR2
MMIO and BAR0 scanout access never rely on the loader's partial bootstrap map.
It also calls `mmio_disable_test_mode()` immediately after early architecture
initialization, before PMM or any hardware access; otherwise uninitialized
freestanding test-mode state redirects device access into test tables.
The function is a real strong owner in `os.kernel.boot.mmio`; evidence builds
must reject the former weak no-op. QEMU native-build discovery is limited to
the generated configuration and production entry while `SIMPLE_LIB=src`
resolves its transitive imports, preventing unrelated library parse failures
from contaminating the production closure.
The host evidence closure likewise avoids SimpleOS `WmService` and generic VFS
ownership: its loop state is host-owned and evidence files use the direct
runtime file facade. The latest isolated stage3 build compiled 260 modules with
zero file failures but still generated 23 unresolved stubs. The wrapper deleted
the linked candidate and recorded `production-native-build-incomplete`; no
launch or screenshot from that artifact is acceptable evidence.
Compositor IPC method numbers are common protocol data rather than an
`os.userlib` dependency. Even after that ownership correction, a clean stage3
entry-closure build compiled 271 modules and retained the identical 23-symbol
set, so the remaining host blocker is tracked as compiler reachability rather
than bypassed with runtime stubs.
