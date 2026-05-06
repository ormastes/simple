<!-- codex-design -->

# Architecture: SimpleOS Wine Substrate

Date: 2026-05-06

## Architectural Decision

Use a layered compatibility substrate before attempting Wine itself. The architecture is a set of native SimpleOS capabilities plus compatibility adapters:

1. native SimpleOS process, VM, IPC, filesystem, and renderer services;
2. Simple lib POSIX-like adapter surface;
3. Wine substrate capability matrix and diagnostics;
4. PE/COFF loader and NT process bootstrap experiments;
5. eventual Wine integration.

Async waits and file/network I/O are not a separate subsystem in this plan.
Wine-facing adapters sit above `nogc_async_mut.async.future.Future`,
`nogc_async_mut.io.driver.IoDriver`, `nogc_async_mut.io.event_loop.EventLoop`,
and `nogc_async_mut.io.event_loop.Waker`.

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

## Boundary Rules

- Wine-facing code depends on compatibility adapters, not raw kernel internals.
- Compatibility adapters depend on native services, not Wine concepts.
- Compatibility adapters reuse `nogc_async_mut`; new Wine-specific runtimes are out of scope.
- Renderer and WM expose backend semantics through shared compositor/input interfaces.
- PE parsing is pure data validation until VM/process safety gates are verified.

## Risks

- A direct upstream Wine port before pthread/dynamic-loader/VM work will stall.
- A fake X11 surface that only paints pixels will not satisfy Wine window/message semantics.
- Containers without VM and namespace isolation are not a Wine safety boundary.
- A `hello.exe` success without import, TLS, relocation, and subsystem validation is misleading.
