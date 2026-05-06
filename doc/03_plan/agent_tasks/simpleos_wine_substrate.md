<!-- codex-design -->

# Agent Task Breakdown: SimpleOS Wine Substrate

Date: 2026-05-06

## Phase 0: Audit And Capability Matrix

- Create the Wine substrate capability matrix and verification manifest.
- Link current SimpleOS evidence and blockers.
- Do not mark unknown rows complete.

## Phase 1: Process Baseline

- Remove resident fallback from desktop app acceptance.
- Re-run QEMU desktop process-backed app evidence.
- Stabilize process reap/fault observation.

## Phase 2: POSIX Simple Lib Adapter

- Implement fd/process/stdio/timer/socket/path/error adapter APIs.
- Add compatibility tests and docs.

## Phase 3: Threads And TLS

- Replace pthread no-op stubs with real kernel/user support.
- Add synchronization wait objects and per-thread fault attribution.

## Phase 4: VM And Containers

- Add reserve/commit/protect/unmap and guard-page behavior.
- Add namespace-backed container boundaries.
- Verify fixed mappings and execute permissions.

## Phase 5: Renderer And WM Backend

- Upgrade 2D renderer and WM event model to X11-class behavior.
- Add damage, expose, clipboard, input/focus, cursor, text, and parity tests.

## Phase 6: Dynamic Loading And PE Parser

- Define dynamic loading path.
- Implement safe PE/COFF parser before any execution.

## Phase 7: Non-GUI `hello.exe`

- Add known PE32+ console fixture.
- Run parse/map/import gates.
- Execute only after VM/process/thread/import safety gates pass.

