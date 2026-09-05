<!-- codex-research -->
# Tiny UI/Web/WM local research

Date: 2026-08-14

## Decision context

The tiny stack is a strict profile of existing Simple UI semantics. It is not a replacement framework. Tiny WM is mandatory because the deliverable is an interactive fullscreen embedded product, not only a renderer.

## Reusable repository contracts

- `src/lib/common/ui/widget_kind.spl` is the naming and semantic census for controls. Tiny implementations should preserve compatible public names through generated aliases and a mapping manifest.
- `doc/04_architecture/ui/shared_ui_contract.md` establishes shared TUI/GUI/Web semantics and makes full DrawIR additive rather than universally mandatory.
- `src/lib/common/ui/window_scene.spl` already carries content-frame parent IDs and offsets. It is the source for parent-relative compatibility adapters.
- `src/os/compositor/compositor.spl` combines lifecycle, focus, capture, drag/resize, fullscreen, browser/GUI content, clipboard, effects, and rendering. It is an extraction source and differential oracle, but is too broad for the 409,600-byte closure.
- `src/os/compositor/display_backend_core.spl` and `src/os/compositor/input_backend.spl` provide useful present/input semantics to narrow into versioned ports.
- `src/app/ui.tui/screen.spl` is ANSI/string oriented. Tiny TUI needs a fixed cell buffer and bounded terminal encoder.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` is a full renderer oracle. Its animation, material, hit-index, diagnostic, and full DrawIR dependencies must not enter the tiny base.
- `src/os/apps/simple_browser/main.spl` demonstrates a freestanding browser path but does not prove a general Tiny WM-backed SimpleOS application or the size target.
- Current `.sfm` and dynSMF facilities are usable deployment foundations. The proposed typed facet/aspect runtime is not a prerequisite.
- RV32 QEMU contracts use `riscv32-unknown-none`, `qemu-system-riscv32`, the `virt` machine, and `rv32`; fresh lane-owned build, boot, framebuffer, and input evidence is still required.

## Extraction conclusion

The smallest stable seam is:

```text
Tiny GUI/Web/TUI semantics -> TinyPane -> TinyDrawStream
                                      -> software/Vulkan backend
                                      -> Tiny WM kiosk
                                      -> present/input ports
```

Tiny WM owns root/popup surfaces, focus, pointer capture, damage, composition policy, and presentation. Tiny 2D owns raster execution. Full compositor, DrawIR, WebIR, rich font, desktop shell, and service IPC remain optional compatibility or feature packs.

## Principal risks

1. Empty RV32 runtime overhead may consume the feature budget before UI work begins.
2. Text-heavy registries, generic specialization, broad re-export hubs, and per-class shared objects can retain large closures.
3. Reusing the full compositor or web renderer directly defeats isolation and size measurability.
4. A launcher-only measurement can conceal mandatory dynamic modules; the cold-start closure must also fit.
5. QEMU `virt` availability does not itself prove a framebuffer, virtio-gpu, or physical input path.
6. Concurrent workspace churn previously invalidated target evidence; RV32 work needs owned outputs and recorded hashes.

## Recommended first slice

Measure an empty no-GC RV32 image, freeze TinyRect/TinyPane/TinyEvent/TinyDrawStream/TinyModuleV1/Tiny WM ports, then prove one nested scrolling pane, button, popup, focus, pointer hit, and software-rendered fullscreen host frame before adding HTML parsing or optional backends.

## 2026-08-16 integration observation

The isolated Tiny WM unit path produced a correct direct-present receipt while the integrated browser path did not. The browser copied class-valued retained WM/present owners into locals, mutated the copies, then assigned them back. The bounded repair mutates `self.wm` and `self.present` directly and adds an integration assertion that the retained browser-owned WM still contains the fullscreen root after rendering. This is a source-level hypothesis until the recorded pure-Simple unit/integration commands pass once.
