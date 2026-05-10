<!-- codex-research -->

# Domain Research: Wine Prerequisites For SimpleOS

Date: 2026-05-06

## Wine Architecture Facts

- Wine targets POSIX-compliant operating systems such as Linux, macOS, and BSD; it translates Windows API calls into POSIX/native host calls rather than emulating a CPU.
- Wine includes a program loader/preloader, core DLL implementations, `ntdll`, `kernel32`, `user32`, programs, native tools, and `wineserver`.
- `ntdll` is central: in Wine it interfaces to `wineserver` or the Unix kernel and contains the PE dynamic linker.
- Startup uses the host dynamic loader for `ntdll.dll.so`, creates PEB/TEB state, connects to or launches `wineserver`, creates the process heap, maps PE file sections, applies relocations, builds a new PE stack, resolves DLL imports, initializes TLS, then enters the PE entry point.
- Wine process creation historically relies on Unix process inheritance and server-mediated state passing. Modern ports can adapt, but equivalent process creation, handle inheritance, address-space, and server IPC semantics are mandatory.
- Wine translates Unix signals and CPU context into Windows exceptions/SEH, so the host OS needs robust per-thread signal/fault delivery, register context access, guard pages, and stack handling.

## Practical Dependency Surface

Minimum credible Wine host substrate:

- C toolchain and build system able to build Wine and PE-format DLLs, including MinGW cross compilation.
- POSIX-like processes, environment, argv, file descriptors, pipes, sockets, timers, polling/select-like waits, errno/error mapping, and filesystem namespace.
- Native threads with TLS, synchronization, waits, and per-thread exception/fault state.
- Virtual memory primitives: mmap/protect/unmap equivalents, fixed-address mappings, guard pages, executable mappings, page faults, and per-process address spaces.
- Dynamic linking or a deliberate Wine-specific loader replacement for Unix-side `.so` pieces.
- IPC suitable for `wineserver` object/handle/message/synchronization semantics.
- Filesystem semantics for Windows path mapping, drive mappings, case behavior strategy, long names, short 8.3 names, attributes, locking, and sharing modes.
- Graphics/window backend: X11 or Wayland-compatible driver surface, plus input, clipboard, cursors, display modes, and window message integration.
- OpenGL and/or Vulkan if the goal includes real applications/games; many GUI apps can start lower, but useful Wine quickly reaches this layer.
- Font/text stack, audio backend, crypto/TLS, multimedia, HID, USB, printing, and device discovery depending on application class.

## Primary Sources

- WineHQ home: https://www.winehq.org/
- Wine build dependencies wiki: https://gitlab.winehq.org/wine/wine/-/wikis/Building-Wine
- Wine source tree structure wiki: https://gitlab.winehq.org/wine/wine/-/wikis/Source-Tree-Structure
- Wine Developer Guide mirror: https://fast-mirror.isrc.ac.cn/winehq/wine/docs/en/winedev-guide.html

