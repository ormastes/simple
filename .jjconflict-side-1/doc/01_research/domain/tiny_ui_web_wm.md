<!-- codex-research -->
# Tiny UI/Web/WM domain research

Date: 2026-08-14

## Reference findings

- FTXUI separates component, DOM element, and screen concerns. It is suitable as a host differential oracle for retained controls and cell output, but must not be linked into the embedded product.
- litehtml separates document/layout behavior from host drawing through `document_container`. Tiny Web should preserve that boundary with a much smaller bounded `TinyWebHostPortV1`, not port the C++/STL object graph or full callback surface.
- Weston kiosk shell distinguishes fullscreen single-application shell policy from reusable compositor machinery. This supports a mandatory kiosk Tiny WM with optional desktop policy packs.
- QEMU documents RISC-V system emulation and the generic `virt` board. Display and input remain guest-driver integration work rather than implied platform capabilities.
- Vulkan's loader/driver separation supports Tiny Vulkan as a backend client of an existing loader or OS GPU service. The base RV32 acceptance path remains software.
- LLVM LTO and linker garbage collection help close unused code, but acceptance must use stripped binary, PT_LOAD, section, symbol, and dependency evidence.

## Primary sources

- FTXUI architecture: <https://arthursonzogni.github.io/FTXUI/ftxui.html>
- FTXUI components: <https://arthursonzogni.github.io/FTXUI/module-component.html>
- litehtml: <https://github.com/litehtml/litehtml>
- Weston kiosk shell: <https://wayland.pages.freedesktop.org/weston/toc/kiosk-shell.html>
- Libweston: <https://wayland.pages.freedesktop.org/weston/toc/libweston.html>
- QEMU RISC-V: <https://www.qemu.org/docs/master/system/target-riscv.html>
- QEMU `virt`: <https://www.qemu.org/docs/master/system/riscv/virt.html>
- Vulkan loader guide: <https://docs.vulkan.org/guide/latest/loader.html>
- Vulkan loader architecture: <https://github.com/KhronosGroup/Vulkan-Loader/blob/main/docs/LoaderInterfaceArchitecture.md>
- LLVM LTO: <https://llvm.org/docs/LinkTimeOptimization.html>
- GNU ld options: <https://sourceware.org/binutils/docs/ld/Options.html>

## Adopted implications

The product remains pure Simple and bounded. External projects are references and oracles only. Optional accelerators and compatibility exports cannot become base imports, and no backend is allowed to report success after silently selecting another implementation.
