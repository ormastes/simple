# Plan: SimpleOS L4/Exokernel Platform for Simple Language

**Date:** 2026-04-04
**Status:** In Progress (Workstream C Phase 1-5 substantially complete; Workstreams A+B pending)
**Research:** [local/simpleos_l4_exokernel_platform.md](../01_research/local/simpleos_l4_exokernel_platform.md)

## Objective

Turn SimpleOS from a kernel demo into a usable L4-style microkernel platform with exokernel-style user drivers, async-first services, a GPU-accelerated GUI stack, and a credible path for LLVM/Clang and Rust portability.

The end-state is not just "boot to framebuffer". The end-state is:

- a protected-capability kernel
- user-space device drivers, including GPU
- a GPU-backed rendering path for the UI library
- a browser-style rendering library reused by the GUI layer
- a primitive but usable desktop shell
- a macOS-like lower task bar / dock
- at least one launchable Hello World window app with keyboard shortcut launch
- reusable logic extracted into Simple libraries instead of duplicated app-local code

## Current Baseline

Already present in the repo:

- kernel object groundwork in `src/os/kernel/types/`
- notification and message-buffer groundwork in `src/os/kernel/ipc/`
- POSIX compatibility groundwork in `src/os/posix/`
- QEMU scenario support in `src/os/qemu_runner.spl`
- desktop/compositor groundwork in `src/os/compositor/` and `src/os/desktop/`
- GUI porting notes in `src/os/port/gui/README.md`
- LLVM and Rust porting notes in `src/os/port/llvm/README.md` and `src/os/port/rust/README.md`
- browser-style and GPU-related library pieces in `src/lib/gc_async_mut/gpu/browser_engine/`, `src/lib/nogc_sync_mut/web_ui/`, `src/lib/nogc_sync_mut/gpu_driver/`, and related `gpu` modules
- kernel-side exokernel primitives, IRQ routing, PCI/device grant wiring, and user-space driver groundwork have already advanced beyond the original short plan

The main gap is not ideas. The main gap is a coherent delivery sequence and clean module boundaries.

## Target System Shape

### Kernel owns

- protection domains
- scheduling
- capability validation
- memory mapping and revocation
- IRQ routing
- DMA / IOMMU mediation
- IPC / notification fast paths

### User-space services own

- PCI enumeration policy
- storage, network, and GPU drivers
- display service and compositor policy
- desktop shell policy
- app launch policy
- UI toolkit and higher-level rendering

### Desktop stack

The desktop stack must converge on one rendering pipeline:

1. application UI tree or browser-style DOM/tree
2. shared scene/display list library
3. GPU client library
4. GPU user driver command transport
5. virtio-gpu backed scanout in QEMU first

The framebuffer-only path remains only as bootstrap and fallback.

## Architecture Constraints

1. Kernel remains policy-thin.
2. GPU is a user-space driver, not a permanent kernel driver.
3. Async is the default contract across driver, display, compositor, and GUI boundaries.
4. QEMU support is a design target, not an afterthought.
5. Shared logic must be extracted into libraries before feature-specific duplication appears.
6. Browser-style rendering and widget rendering must converge on shared primitives instead of building parallel raster stacks.
7. Every phase must end with executable validation, not documentation-only completion.

## Program Split: 3 Workstreams

The implementation program is explicitly split into three top-level workstreams so GUI work, userland/workstation work, and core platform work can proceed in parallel without collapsing into one mixed backlog.

### Workstream A: GUI / Desktop / Browser Rendering

Scope:

- display service
- GPU user driver consumption
- compositor
- primitive window manager
- dock / launcher / shortcuts
- GUI library
- browser-backed rendering reuse
- Hello World window app

Primary phases:

- Phase 7
- Phase 8
- Phase 9
- Phase 10
- Phase 11
- Phase 12

### Workstream B: File / Bash / SSH / Userland

Scope:

- VFS closure
- filesystem write support and app asset loading
- terminal emulator and shell user experience
- bash-like command surface and scripting direction
- SSH / remote terminal / remote execution integration
- launcher/runtime expectations for desktop apps and CLI tools

Primary phases:

- Phase 6
- Phase 13
- Phase 14

Additional planning note:

- "bash" here means shell-userland compatibility and interactive workflow, not necessarily GNU Bash binary compatibility on day one.
- SSH and remote-terminal work should align with the dispatch/module shape already described in `doc/04_architecture/t32_terminal_power_remote.md`.

### Workstream C: Core Platform / Drivers / Toolchains / Other

Scope:

- kernel completion
- capability and revoke model
- PCI and driver supervisor
- async driver runtime
- storage/network driver model
- LLVM/Clang port
- Rust port
- SDK/sysroot/toolchain packaging

Primary phases:

- Phase 1
- Phase 2
- Phase 3
- Phase 4
- Phase 5
- the platform-facing parts of Phase 6 and Phase 14

## Cross-Check with Existing OS Plans and Reports

This plan must stay consistent with nearby OS-specific documents already in the repo.

### Checked documents

- `doc/03_plan/os_gui_hello_world.md`
- `doc/09_report/simpleos_status_2026-04-02.md`
- `doc/04_architecture/t32_terminal_power_remote.md`

### Alignment decisions

- The existing GUI hello-world plan is now treated as an early bootstrap subproblem inside Workstream A, not as the full desktop target.
- The status report's current assessment still holds:
  - x86_64 GUI is the only realistic near-term graphical target
  - FAT32/VFS and networking are incomplete enough that userland/file/SSH work needs its own track
  - the browser work is still mostly type/model level and therefore must remain behind the GUI MVP, not ahead of it
- Terminal/SSH work is recognized as a first-class userland lane rather than an afterthought under "tools".

### Planning rule

When one of the checked documents changes materially, this plan should be updated rather than allowed to drift. The main consistency checks are:

- GUI boot path assumptions
- compositor and desktop-shell capabilities
- filesystem/VFS maturity
- terminal/SSH module boundaries
- QEMU readiness claims

## Proposed Shared Libraries

These are the primary extractions required by this plan. Names are proposed; exact placement can be adjusted during implementation, but shared logic must not stay embedded in one app or one service.

### Core OS protocol and runtime libraries

- `src/os/userlib/ipc_protocol.spl`
  - extend as the stable IPC envelope for kernel, drivers, compositor, and apps
- `src/os/userlib/device.spl`
  - expand into the user-side device grant, BAR mapping, IRQ wait, DMA window API
- `src/os/userlib/process.spl`
  - app launch, capability handoff, shortcut dispatch helpers

### New proposed shared libraries

- `src/lib/common/gpu_protocol/`
  - command queue structures, fence protocol, error/status codes, pixel formats, buffer/surface descriptors
- `src/lib/common/display_protocol/`
  - display head, mode set, scanout surface, cursor plane, damage rectangle contracts
- `src/lib/common/window_protocol/`
  - window IDs, focus events, shortcut routing, dock/app launcher contracts
- `src/lib/common/render_scene/`
  - scene graph or display list primitives shared by browser renderer, widget toolkit, and compositor
- `src/lib/common/text_layout/`
  - glyph runs, shaping hooks, line breaking, clipping, font fallback metadata

### GPU and rendering libraries

- `src/lib/nogc_async_mut/gpu_driver/`
  - make this the async user-mode GPU client library, not only a placeholder module
- `src/lib/nogc_sync_mut/compositor/`
  - reuse for surface and command structures where sync logic is more appropriate
- `src/lib/gc_async_mut/gpu/engine2d/`
  - source of 2D acceleration primitives and fallback backend split
- `src/lib/gc_async_mut/gpu/browser_engine/`
  - browser-style layout/paint pipeline to be reused by the GUI library
- `src/lib/nogc_sync_mut/web_ui/`
  - adapt existing web_ui abstractions into a native-SimpleOS frontend bridge rather than a browser-only concept

### OS-side service libraries

- `src/os/services/display/`
  - display server protocol handling, mode setting, scanout ownership
- `src/os/services/wm/`
  - primitive window manager policy, focus, tiling/floating rules, shortcut dispatch
- `src/os/services/launcher/`
  - app registry, shortcuts, dock integration, app spawning
- `src/os/lib/gui/`
  - shared widget runtime and GPU rendering bridge for all GUI apps

## Phase Plan

## Phase 0: Completed Baseline

Completed already and retained as prerequisites:

- codegen fixes
- kernel object groundwork
- capability checks
- notification objects
- IPC shared buffers
- QEMU scenario framework
- initial POSIX compatibility layer

This phase is done, but every later phase may uncover follow-up fixes in those areas.

## Phase 1: Kernel Completion for Exokernel Delivery

Purpose: finish the kernel mechanisms needed by user-mode drivers and multi-service GUI execution.

### Deliverables

- finalize `DeviceGrant`, `IrqObject`, `DmaWindow`, and `IommuDomain` semantics in `src/os/kernel/types/device_mem_types.spl`
- add device grant syscalls for:
  - BAR mapping
  - IRQ binding/unbinding
  - DMA window creation/revocation
  - device memory revoke on driver restart
- add capability revocation path for dead or restarted services
- add async wait primitives so driver tasks can block on IRQ, notification, or fence completion without busy polling
- add fault-domain separation for restartable user drivers

### Acceptance

- a user process can be granted and then revoke PCI BAR, IRQ, and DMA access
- a crashed driver does not require kernel reboot
- kernel logs show clean capability revoke and service restart

## Phase 2: PCI and Driver Supervisor Capsules

Purpose: create the service topology that all later storage/network/GPU work depends on.

### Deliverables

- `src/os/services/pcimgr/`
  - PCI discovery policy
  - capability issuance to specific driver processes
  - per-function metadata registry
- `src/os/services/driver_supervisor/`
  - spawn, monitor, and restart drivers
  - health pings and crash records
- `src/os/services/device_registry/`
  - map logical classes to active driver endpoints

### Acceptance

- QEMU `q35` boot enumerates expected PCI devices
- the supervisor can restart a synthetic failing test driver
- other services resolve drivers by registry rather than hardcoded endpoints

## Phase 3: Async Driver Runtime and Common Driver Kit

Purpose: make every user-space driver share the same runtime and protocol model.

### Deliverables

- `src/os/lib/driver_runtime/` proposed
  - event loop over notification + IRQ + IPC
  - zero-copy queue helpers over shared message buffers
  - fence/wait abstractions
  - restart-safe init handshake
- `src/lib/common/gpu_protocol/` and `src/lib/common/display_protocol/`
  - first protocol consumers
- standard driver lifecycle:
  - probe
  - claim
  - init
  - publish endpoints
  - serve async requests
  - quiesce
  - restart

### Acceptance

- storage/network/GPU drivers can share the same runtime crate/module pattern
- no driver uses ad hoc polling loops when notifications are available

## Phase 3.5: Async Exokernel Services — COMPLETE (2026-04-04)

Purpose: notification-driven async I/O throughout the OS stack. Dual interface: POSIX sync + Simple-native async.

### Deliverables (all complete)

- **OS Async Runtime** (`src/os/async/`, 8 files): OsFuture, OsExecutor (notification-based sleep), SpscRing, WaitAny
- **Kernel WaitAny syscall 29**: multiplex wait on up to 4 notifications
- **Async NVMe Driver**: `BlockDevice`/`AsyncBlockDevice` traits, notification-based completion
- **Async VirtIO-Net Driver**: `NetworkDevice`/`AsyncNetworkDevice` traits, async frame I/O
- **Async Filesystem + FAT32 Write**: `AsyncFilesystem` trait, VFS IPC service (port 1), LRU block cache, FAT32 write (create/delete/rename)
- **TCP/IP Stack** (`src/os/services/netstack/`, 10 files, 3739 lines): Ethernet/ARP/IPv4/ICMP/UDP/TCP (full RFC 793), socket API, NetstackService (port 2, libOS pattern)
- **POSIX Layer Completion**: fd_io wired to VFS IPC, pipes (ring buffer + notifications), posix_spawn/waitpid, posix_kill, POSIX sockets over netstack IPC, select/poll via WaitAny
- **Async Shell** (`src/os/apps/shell/`, 1034 lines): job control (fg/bg/jobs), pipes, redirection, background execution, bidirectional file access
- **SSH Server** (`src/os/apps/sshd/`, 10 files, 2911 lines): SSH-2 transport, Curve25519-SHA256 kex, AES-256-GCM, password/pubkey auth, channels, PTY emulation
- **Pure Simple Crypto** (`src/os/crypto/`, 5 files, 1984 lines): SHA-256, AES-256-GCM, Curve25519, ChaCha20 CSPRNG

### Acceptance

- Applications use either POSIX sync or async Future API for all I/O
- No polling loops in driver hot paths — all use notification-based wakeup
- TCP/IP stack runs entirely in user-space (exokernel pattern)
- SSH daemon accepts connections on port 22, provides interactive shell
- Shell supports `cmd1 | cmd2 > file &` with job control

## Phase 4: LLVM/Clang Porting Program

Purpose: upgrade the current "README-level" LLVM work into a tracked porting program with staging, ABI validation, and output consumption by SimpleOS.

### Deliverables

- refine `src/os/port/llvm/build.spl` into a repeatable staged build pipeline
- maintain the `ormastes/llvm-project` fork as the authoritative SimpleOS toolchain source
- deliver:
  - target triple recognition
  - Clang driver defaults
  - LLD output/linker-script integration
  - compiler-rt builtins for freestanding SimpleOS
- produce a sysroot layout definition for headers, crt objects, libraries, and linker scripts
- define the first supported C/C++ portability scope:
  - freestanding C
  - limited `libc`/syscall shim
  - no hosted pthread/process expectations initially

### Subphases

- 4A: triple and driver stabilization
- 4B: compiler-rt and crt objects
- 4C: sysroot packaging
- 4D: C smoke tests in QEMU
- 4E: service/app consumption from SimpleOS build tooling

### Acceptance

- `clang --target=x86_64-simpleos` can build and link a freestanding hello binary
- the binary runs under SimpleOS in QEMU
- documented sysroot layout exists and is exercised by automation

## Phase 5: Rust Porting Program

Purpose: make Rust a real secondary systems language for SimpleOS services and libraries, not just a future note.

### Deliverables

- harden `src/os/port/rust/build.spl`
- maintain `ormastes/rust` target support
- support `core` and `alloc` first
- define allocator, panic, startup, and linker integration contract with SimpleOS
- add examples for:
  - `no_std` hello process
  - simple service using IPC
  - driver-side utility crate consuming the common protocol libraries

### Subphases

- 5A: target JSON and linker integration
- 5B: `core` and `alloc` validation
- 5C: startup and panic runtime
- 5D: Rust IPC sample service
- 5E: Rust-on-SimpleOS CI/QEMU smoke coverage

### Acceptance

- a Rust `no_std` hello app boots under SimpleOS
- a Rust process can send and receive a simple IPC message
- Rust and Simple code can coexist in the same image/build graph

## Phase 6: Storage and Network User Drivers

Purpose: validate the user-driver model before the GPU stack depends on it.

**Note:** Phase 3.5 delivered async NVMe and VirtIO-net user drivers with `BlockDevice`/`AsyncBlockDevice` and `NetworkDevice`/`AsyncNetworkDevice` traits. Remaining work: restart behavior validation and service registry integration.

### Deliverables

- ~~NVMe or virtio-blk user driver capsule~~ — **DONE** (Phase 3.5)
- ~~virtio-net user driver capsule~~ — **DONE** (Phase 3.5)
- service registry integration
- fault and restart behavior validation

### Acceptance

- block and network I/O work without kernel-resident drivers — **DONE** (Phase 3.5)
- restart path is proven on at least one driver

### Workstream mapping

- Workstream B owns file-facing integration and user-visible filesystem behavior
- Workstream C owns driver/runtime/device architecture

## Phase 7: GPU User Driver Bring-Up

Purpose: build the first real GPU user driver using the exokernel model and async runtime.

The first target is QEMU-friendly virtio-gpu, not a native hardware stack. That keeps the control plane honest.

### Deliverables

- `src/os/drivers/gpu/` proposed user-mode GPU driver capsule
- driver uses:
  - BAR/device grant mapping
  - IRQ-driven fence completion
  - async command queue submission
  - shared memory / DMA-backed buffers
- initial virtio-gpu support:
  - resource create
  - transfer to host
  - scanout setup
  - flush / fence handling
  - cursor plane if feasible
- `src/os/services/display/`
  - display mode and scanout owner
  - surface registration
  - damage tracking

### QEMU support requirements

QEMU support must be treated as a product requirement.

- keep `x64-gpu-2d` in `src/os/qemu_runner.spl` as the default GPU scenario
- add explicit validation for:
  - framebuffer bootstrap
  - virtio-gpu resource allocation
  - scanout update
  - fence completion
  - graceful fallback if acceleration path is unavailable

If a feature cannot be exercised in QEMU, it must not block the rest of the GPU pipeline. In that case it is isolated behind a capability and a fallback path.

### Acceptance

- QEMU displays a GPU-driven scanout, not only a legacy framebuffer path
- the GPU driver runs entirely in user space
- screen updates are IRQ/fence driven, not busy-loop polled

## Phase 8: GPU Acceleration Abstraction for UI and Browser Rendering

Purpose: create one reusable acceleration layer for both the widget toolkit and the browser-style renderer.

### Deliverables

- `src/lib/common/render_scene/`
  - shapes, text runs, images, clipping, transforms, z ordering
- `src/os/lib/gui/`
  - widget tree to render scene conversion
- integrate `src/lib/gc_async_mut/gpu/browser_engine/`
  - DOM/layout/paint output converted to the same render scene abstraction
- GPU backend bridge:
  - scene upload
  - texture atlas upload
  - glyph cache upload
  - draw command batching
- software fallback remains available via framebuffer for bootstrap and tests

### Rule

The GUI library and the browser renderer must not each own a separate paint/raster abstraction. They must meet at the shared render-scene layer and diverge only in input model and layout logic.

### Acceptance

- one scene API can render both a widget-based Hello World app and a browser-style layout sample
- CPU and GPU backends produce functionally equivalent output at the scene level

## Phase 9: Native GUI Library on Top of Browser Rendering Library

Purpose: make the GUI stack use the browser rendering work instead of competing with it.

### Deliverables

- adapt the existing browser-style pieces in:
  - `src/lib/gc_async_mut/gpu/browser_engine/`
  - `src/lib/nogc_sync_mut/web_ui/`
- define the native GUI library architecture:
  - widget tree input
  - widget-to-DOM or widget-to-scene bridge
  - style/theme model
  - event routing
- use browser-engine layout/paint when advantageous for:
  - text layout
  - box layout
  - clipping
  - image composition

### Practical target

The GUI library should expose ergonomic native Simple APIs, while internally reusing browser-engine pieces where they already solve:

- layout
- paint ordering
- style propagation
- text/image composition

### Acceptance

- one sample GUI app renders through the browser-backed pipeline
- no app has to manually interact with GPU protocol details

## Phase 10: Compositor, Primitive Window Manager, and Dock

Purpose: move from "multiple surfaces" to a minimally coherent desktop.

### Deliverables

- evolve `src/os/compositor/` from framebuffer compositor to display-service client
- add `src/os/services/wm/`
  - floating windows first
  - focus management
  - raise/lower
  - move/resize
  - close/minimize
- keep the implementation primitive on purpose:
  - no advanced tiling in first cut
  - no complex animations required for MVP
- update `src/os/desktop/`
  - convert current taskbar/dock groundwork into a macOS-like lower dock
  - launcher + running apps + focus indicator + clock/system area

### Explicit desktop MVP

- bottom dock
- launcher panel
- shortcut handling
- single desktop background
- multiple overlapping windows
- focus follows click
- dirty-rect or damage-based redraw path

### Acceptance

- open, focus, move, and close at least three windows
- launch apps from dock and keyboard shortcut
- compositor redraw uses damage/fence logic rather than full-screen brute force for every event where practical

### GUI implementation note

This phase supersedes the older "taskbar strip" direction. The default target is a lower dock / launcher model, with a primitive window manager behind it. Existing `src/os/desktop/` code should be refactored toward that target rather than preserved as a permanent taskbar-first architecture.

## Phase 11: Hello World Window App and Shortcut Launch

Purpose: force the entire stack to work end to end.

### Deliverables

- `src/os/apps/hello_world/` proposed
  - manifest
  - icon
  - GUI window content
  - keyboard shortcut, for example `Meta+H` or `Ctrl+Alt+H`
- app launch path via:
  - launcher service
  - dock click
  - keyboard shortcut
- window uses the shared GUI library, not a one-off surface implementation

### Acceptance

- from a QEMU desktop boot, the user can launch Hello World with a shortcut
- the app opens a decorated window
- closing and reopening it works without rebooting the desktop shell

## Phase 12: Browser-Backed Sample App and Rendering Validation

Purpose: verify that the browser rendering library is not dead code.

### Deliverables

- at least one browser-rendered sample window:
  - static HTML/CSS-like sample, or
  - widget tree converted through the browser path
- compare output across:
  - CPU software backend
  - GPU backend

### Acceptance

- same logical app scene renders on both backends
- text, image, and box composition behave consistently

## Phase 13: POSIX, VFS, and App Runtime Closure

Purpose: finish the runtime gaps that desktop apps and ported toolchains need.

**Note:** Phase 3.5 delivered most of the core infrastructure listed below. Remaining work: app asset/manifest loading, launcher integration, file-manager UX, and script execution model.

### Deliverables

- ~~connect VFS to POSIX layer~~ — **DONE** (Phase 3.5: posix_open/read/write/close wired to VFS IPC)
- complete enough process and file semantics for:
  - launcher
  - app loading
  - dynamic resource loading
  - toolchain-produced binary execution
- keep "no `fork` by design" unless there is a strong later reason to change it
- ~~document async-native alternatives to `select`/`poll`~~ — **DONE** (Phase 3.5: select_compat.spl via WaitAny, OsExecutor)
- ~~add shell-userland closure for:~~
  - ~~terminal session lifecycle~~ — **DONE**
  - ~~shell command execution~~ — **DONE** (async shell with job control)
  - script execution model
  - ~~remote shell / SSH entry points~~ — **DONE** (SSH server with PTY)
  - file-manager and shell coexistence over the same VFS/process APIs

### File / Bash / SSH split

This phase is intentionally grouped as one userland lane with three subtracks:

- File
  - writable filesystem path
  - manifests/assets/config loading
  - file manager and shell file operations
- Bash / shell
  - command dispatch
  - pipelines/redirection model if added
  - interactive shell UX inside terminal app
- SSH / remote
  - remote terminal sessions
  - secure transport integration
  - eventual desktop or shell remote-control entry points

### Acceptance

- GUI apps can load assets and manifests through the service boundary
- launcher and app runtime do not depend on host-side shortcuts or hardcoded content
- terminal, shell, and remote-session features share the same process/VFS contracts instead of each inventing custom I/O paths

## Phase 14: Packaging, Sysroots, SDK, and Developer Workflow

Purpose: make the platform usable by others.

### Deliverables

- package SimpleOS SDK headers and libraries under `src/os/sdk/`
- define sysroot and library packaging for:
  - Simple
  - Clang/LLVM
  - Rust
- add example templates:
  - GUI app
  - browser-backed app
  - service
  - user-space driver

### Acceptance

- one command path exists to build and boot the desktop image in QEMU
- sample apps can be added without patching core OS files

## Dependency Order

Hard dependencies:

- Phase 1 before Phase 7
- Phase 2 before Phase 6 and Phase 7
- Phase 3 before every production user-space driver
- Phase 7 before Phase 8 GPU acceleration
- Phase 8 before Phase 9 GUI acceleration
- Phase 9 before Phase 10 desktop polish
- Phase 10 before Phase 11 shortcut-launched Hello World
- Phase 13 before full toolchain-on-OS goals

Can run in parallel with careful ownership:

- Phase 4 LLVM and Phase 5 Rust
- Phase 6 storage/network drivers and early Phase 7 GPU driver control plane
- Phase 8 render-scene work and Phase 10 window-manager policy work

## QEMU Validation Matrix

QEMU is the primary validation environment until real hardware support is ready.

### Required scenarios

- `rv64-base`
- `rv64-dtb-pci`
- `x64-pci-lab`
- `x64-net-user`
- `x64-gpu-2d`
- `x64-gui`

### Desktop validation gates

- boot to shell
- dock visible
- keyboard and mouse active
- Hello World shortcut launch works
- GPU scanout updates visible
- window move/focus/close works
- driver restart does not wedge the system

## Non-Goals for This Plan Revision

These are intentionally excluded from the initial desktop/GPU milestone:

- full OpenGL/Vulkan userspace API exposure
- advanced 3D compositor effects
- sophisticated tiling WM features
- browser compatibility beyond internal rendering reuse
- full hosted POSIX process model
- production-quality font shaping across all scripts

## Risks and Controls

### Risk: duplicated render stacks

Control:

- force widget UI and browser rendering through one shared render-scene layer

### Risk: GPU work becomes kernel work

Control:

- kernel exposes grants and IRQ/DMA mediation only
- virtio-gpu policy and queues stay in the user driver

### Risk: QEMU path diverges from future hardware path

Control:

- isolate transport/device specifics behind `gpu_protocol` and `display_protocol`
- keep virtio-gpu as first backend, not the only backend contract

### Risk: toolchain work blocks OS usability

Control:

- desktop/UI/GPU path must be able to ship with Simple-first apps before LLVM/Rust reach maturity

## Milestone Definition

The first meaningful desktop milestone is complete when all of the following are true:

- SimpleOS boots to a graphical desktop in QEMU
- the display is driven by a user-space GPU driver
- a primitive floating window manager is operational
- a macOS-like lower dock launches apps
- a Hello World GUI app opens from a keyboard shortcut
- the GUI library uses shared browser-rendering pieces and the shared render-scene layer
- reusable logic is factored into libraries rather than hidden inside one app/service

## Immediate Next Steps

1. Expand Phase 1 into syscall/type-level design tasks and identify missing kernel APIs.
2. Create the protocol/library breakdown for `gpu_protocol`, `display_protocol`, `window_protocol`, and `render_scene`.
3. Split the existing desktop/compositor work into:
   - bootstrap framebuffer path
   - display service path
   - window-manager policy path
4. Turn the LLVM and Rust port notes into tracked implementation checklists with smoke tests.
5. Define the `x64-gpu-2d` QEMU acceptance script for the first GPU user-driver milestone.
