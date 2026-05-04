<!-- codex-research -->
# Rust Runtime Minimization - Domain Research

Date: 2026-05-04

## Scope

This research checks whether file I/O, networking, and terminal/TUI support can be implemented without Rust as the default runtime substrate.

## Findings

### OS File I/O Is A C ABI Boundary

POSIX `open()` establishes a file descriptor for later I/O calls and defines flags such as read-only, write-only, read/write, append, create, and truncate. Windows `CreateFileA` creates or opens files and I/O devices and returns a handle. These APIs map cleanly to a small C shim returning Simple runtime values.

Implication: Simple should own file/path policy and error typing; C should own direct syscall/Win32 handle calls.

Sources:

- POSIX `open()`: https://pubs.opengroup.org/onlinepubs/9699919799/functions/open.html
- Windows `CreateFileA`: https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-createfilea

### Networking Can Be C Shims Plus Pure Simple Protocols

POSIX `socket()` returns a file descriptor for a communications endpoint. Windows Winsock similarly creates `SOCKET` objects after address resolution and startup. This supports a split where TCP/UDP sockets are C-core primitives and HTTP/WebSocket/MCP/LSP framing is pure Simple.

Implication: Rust network libraries are not required for basic networking. TLS, async reactors, or HTTP/2+ stacks may still need a selected provider, but that provider should be explicit.

Sources:

- POSIX `socket()`: https://pubs.opengroup.org/onlinepubs/9699919799/functions/socket.html
- Windows Winsock socket setup: https://learn.microsoft.com/en-us/windows/win32/winsock/creating-a-socket-for-the-server

### TUI Requires Terminal Shims, Not A Rust Runtime

POSIX `termios` defines terminal mode structures and control characters. Windows console APIs expose console input/output, screen buffers, pseudoconsole functions, and mode management. These are platform ABI boundaries suitable for C shims.

Implication: TUI layout, event routing, widgets, colors, and escape-sequence composition should be pure Simple. Raw mode, window size, console handles, and platform-specific input decoding should be C-core.

Sources:

- POSIX `termios`: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/termios.h.html
- Windows console functions: https://learn.microsoft.com/en-us/windows/console/console-functions

### Rust `std` Is Broad By Design

Rust `std` provides portable abstractions for I/O, multithreading, and many ecosystem-level conveniences by default. That is valuable for Rust applications but can pull default executable closures toward Rust runtime assumptions when Simple only needs a small set of OS primitives.

Implication: avoid using Rust `std` as the default host abstraction for Simple-generated binaries. Keep Rust lanes opt-in.

Source:

- Rust standard library docs: https://doc.rust-lang.org/std/

## Domain Recommendation

Use a small C platform ABI as the default for OS primitives and put policy/protocol/UI layers in Simple. Reserve Rust for explicitly selected Rust libraries, compiler backend internals, or platform bindings where a Rust implementation is intentionally chosen despite size impact.

