<!-- codex-design -->

# Architecture: SimpleOS Wine Substrate

Date: 2026-05-06

## Architectural Decision

Use a layered MDSOC+ compatibility substrate before attempting Wine itself. The architecture is a set of native SimpleOS capabilities plus compatibility adapters:

1. native SimpleOS process, VM, IPC, filesystem, and renderer services;
2. Simple lib POSIX-like adapter surface;
3. Wine substrate capability matrix and diagnostics;
4. PE/COFF loader and NT process bootstrap experiments;
5. eventual Wine integration.

Async waits and file/network I/O are not a separate subsystem in this plan.
Wine-facing adapters sit above `nogc_async_mut.async.future.Future`,
`nogc_async_mut.io.driver.IoDriver`, `nogc_async_mut.io.event_loop.EventLoop`,
and `nogc_async_mut.io.event_loop.Waker`.

## MDSOC+ Base

This Wine path follows the repo MDSOC+ contract in
`doc/04_architecture/mdsoc_architecture_tobe.md#mdsoc-plus-ecs-business-layer`:

- **MDSOC outer boundary**: each Wine concern is a capsule/facade with a narrow
  public contract. Current common contract nodes live under
  `src/lib/common/wine_*.spl` and `src/lib/common/ui/wine_*.spl`; they must not
  reach into sibling-private SimpleOS service internals.
- **Common tree nodes**: cross-cutting Wine readiness records, gates, PE/NT
  catalog data, VM adapter state, and X11-class facade records stay in
  `src/lib/common/` because they are shared by tests, app probes, and future OS
  services.
- **MDSOC-only kernel and drivers**: page tables, scheduler state, IRQ/device
  state, and low-level VM enforcement remain in `src/os/kernel/` and
  `src/os/drivers/` without ECS.
- **MDSOC+ userland services/apps**: long-lived process, window, container,
  wineserver-like, registry, audio, font, input, and GUI session state must be
  represented as ECS `World` state inside the owning userland capsule, not as a
  monolithic global compatibility struct.
- **Compatibility veneers**: POSIX, Win32, X11-class, and Wine adapters translate
  to native ports/capabilities. They do not own the underlying OS state.

The present `src/lib/common/wine_*` files are therefore contract/facade nodes,
not the final state-owning userland services. When a contract becomes a
resident service, its spec must name the ECS world, components, systems, and
port/capability facade before implementation.

## Layers

### Layer 1: Kernel And VM Primitives

Owns address spaces, page tables, fixed mappings, permission transitions, guard pages, user pointer validation, page faults, thread scheduling, and container namespaces.

### Layer 2: Process And IPC Services

Owns filesystem-backed spawn, process lifecycle, wait/reap, handle tables, IPC ports, object wait semantics, and process-to-WM registration.

### Layer 3: Simple Lib Host ABI

Exposes fd, stdio, cwd/env/argv, pipe, socket, timer, errno, pthread/TLS, and dynamic-loader adapters. Internals stay async/capability-based over the existing `nogc_async_mut` future, completion-driver, event-loop, and waker primitives.

### Layer 4: 2D Renderer And WM Backend

Provides X11-class semantics as native SimpleOS objects: display, screen, window, surface, graphics context, damage region, event queue, input, cursor, clipboard, text, and present.

### Layer 5: PE/COFF And NT Bootstrap

Parses PE/COFF safely, maps image sections only after VM gates pass, resolves imports to controlled NT/Wine shims, initializes PEB/TEB/TLS, and enters only known-safe milestones.

## MDSOC+ Layer Map

| Layer | MDSOC role | ECS role |
|---|---|---|
| Kernel VM/process primitives | MDSOC-only capsule ports for address space, fault, and scheduling contracts | None |
| Drivers and framebuffer/input devices | MDSOC-only device capsules | None |
| WM, process, container, registry, and service daemons | MDSOC outer capsule with typed ports/capabilities | ECS worlds for windows, processes, namespaces, registry keys, handles, audio buffers, font faces, and input events |
| `src/lib/common/wine_*` adapters | Common tree-node facades shared by tests/apps/services | No owned long-lived state; only typed records used as evidence |
| Wine/Win32/X11-class app probes | MDSOC app capsule boundary | ECS only for app/session state when a probe becomes resident |

## Boundary Rules

- Wine-facing code depends on compatibility adapters, not raw kernel internals.
- Compatibility adapters depend on native services, not Wine concepts.
- Compatibility adapters reuse `nogc_async_mut`; new Wine-specific runtimes are out of scope.
- Renderer and WM expose backend semantics through shared compositor/input interfaces.
- PE parsing is pure data validation until VM/process safety gates are verified.
- Shared contract types move upward into `src/lib/common/`; sibling services
  consume them through facades rather than importing each other's private state.
- Resident userland service state follows MDSOC+ ECS. Kernel, drivers, and thin
  ABI veneers remain MDSOC-only or stateless by design.

## Risks

- A direct upstream Wine port before pthread/dynamic-loader/VM work will stall.
- A fake X11 surface that only paints pixels will not satisfy Wine window/message semantics.
- Containers without VM and namespace isolation are not a Wine safety boundary.
- A `hello.exe` success without import, TLS, relocation, and subsystem validation is misleading.
