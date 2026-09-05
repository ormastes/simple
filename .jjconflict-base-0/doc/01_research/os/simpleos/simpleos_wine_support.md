<!-- codex-research -->

# Local Research: SimpleOS Wine Support

Date: 2026-05-06

## Question

Can SimpleOS start a Wine implementation now, or are OS/framework prerequisites missing?

## Current SimpleOS Capabilities

- x86_64 is the only credible target for Wine-class work today. Existing reports mark non-x86_64 HALs as stubbed and the x86_64 kernel path as the primary working lane.
- Desktop and disk smoke evidence exists. The FR-SOS-024 lane boots, mounts FAT32, initializes the desktop, saves through the editor, verifies through CLI, reaches `TEST PASSED`, and has no crash markers.
- Networking is partly strong: the SimpleOS report lists Ethernet, ARP, IPv4, ICMP, UDP, TCP, sockets, and an IPC-backed netstack service.
- GUI/window-manager scaffolding exists, with framebuffer/desktop-ready and resident app materialization evidence.
- A SimpleOS sysroot/cross-toolchain lane exists for LLVM/Clang and staged Rust reporting.

## Blocking Gaps For Wine

- Process-backed apps are not yet closed. The latest desktop disk proof still shows resident fallback markers and lacks direct process-backed app markers.
- Process isolation is partial. Demand paging, page-fault handling, TSS.RSP0/SYSCALL hardening, and live re-verification remain incomplete.
- App ABI is not complete enough for normal programs: file descriptors, process APIs, stdio, timers, IPC, and error mapping are listed as incomplete.
- pthread support is explicitly a no-op stub, and the kernel supports one thread per process.
- Dynamic linking is missing. The repo states static linking only and no `dlopen`/`dlsym`.
- POSIX/VFS is partial: SimpleOS has useful pieces, but stable generic byte streams, filesystem namespace, descriptor semantics, and process app launch are not yet finished.
- Graphics is below Wine needs. SimpleOS has desktop/WM/fb/VirtIO-GPU work, but not X11, Wayland, GLX/OpenGL, Vulkan loader/ICD, or mature input/clipboard/window protocol compatibility.
- Audio, font, crypto/cert, HID, dbus-like device discovery, printing, and multimedia service surfaces are not proven as Wine-compatible host APIs.

## Local Conclusion

SimpleOS can start a Wine feasibility spike, but not a real Wine port. The immediate work should be an OS substrate milestone, not importing Wine wholesale.

