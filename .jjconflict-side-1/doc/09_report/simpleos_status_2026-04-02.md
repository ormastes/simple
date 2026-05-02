# SimpleOS Status Report -- 2026-04-02

## 1. Boot Status per Architecture

| Architecture | Entry Point | Boot Method | Serial | Framebuffer | GUI Entry | Status |
|-------------|-------------|-------------|--------|-------------|-----------|--------|
| **x86_64** | `arch/x86_64/entry.spl` | Multiboot2/Limine | COM1 0x3F8 | Limine LFB | `gui_entry.spl` | Working (serial + FB fill proven) |
| **arm64** | `arch/arm64/entry.spl` | Device tree | UART | -- | -- | Stub only |
| **riscv64** | `arch/riscv64/entry.spl` | SBI | UART | -- | -- | Stub only |
| **riscv32** | `arch/riscv32/entry.spl` | SBI | UART | -- | -- | Stub only |

**x86_64** is the only architecture with a GUI entry point (`gui_entry.spl`). The others have text-mode serial entry points only.

### x86_64 Boot Chain
```
_start() [gui_entry.spl]
  -> serial_init() (COM1 at 0x3F8)
  -> X86Boot.build_boot_output() (memory map, framebuffer info from Limine)
  -> GDT load
  -> gui_kernel_main(boot_info) [gui_main.spl]
       -> FramebufferDriver.from_boot_info(fb_info)
       -> Ps2Keyboard.new() + init()
       -> Ps2Mouse.create(w, h) + init()
       -> Compositor.new(fb, keyboard, mouse)
       -> DesktopShell.new(compositor) + init()
       -> shell.launch_app("Terminal")
       -> shell.run()  [event loop]
```

---

## 2. GUI Compositor Status

**Status: Implemented, untested on hardware**

### Compositor (`src/os/compositor/compositor.spl`)
- Window management: create, destroy, focus, move, resize, Z-order
- Double-buffered rendering via `FramebufferDriver.swap_buffers()`
- Mouse cursor rendering with hotspot
- Window decorations (title bar, close button, border) via `decorations.spl`
- Widget rendering per window via `fb_backend.spl` (font rendering at char level)
- Input routing: keyboard events to focused window, mouse hit-testing
- Drag support: title bar drag to reposition windows
- Keyboard shortcuts: Alt+Tab (cycle focus), Alt+F4 (close), Alt+F5 (minimize)
- Main loop: `run_loop()` polls input + renders each frame

### Desktop Shell (`src/os/desktop/shell.spl`)
- Taskbar: pinned bottom strip with Apps button, window list, clock, system tray
- App launcher: category-grouped application manifest list
- Built-in apps: Calculator, Clock, Terminal
- Window cascading: new windows offset by 30px per existing window
- Taskbar auto-refresh: updates window list on each frame

### What's Needed
- Real hardware/QEMU test with Limine boot
- Timer interrupt for clock updates (currently shows "00:00")
- Wallpaper image loading (currently solid color desktop background)
- Window minimize/restore (toggle visibility implemented, no taskbar restore button)

---

## 3. File System Status

### FAT32 (`src/os/services/fat32/fat32.spl`)

**Status: Read-only implementation complete**

| Operation | Status |
|-----------|--------|
| `mount` | Working -- parses BPB, computes data region |
| `open` | Working -- path resolution via cluster chain traversal |
| `read` | Working -- follows FAT chain, cluster-level reads |
| `readdir` | Working -- lists 8.3 directory entries |
| `stat` | Working -- returns FsNode with size/permissions |
| `seek` | Partial -- computes offset but does not recompute current cluster |
| `write` | Not implemented (returns error) |
| `mkdir` | Not implemented (returns error) |
| `rmdir` | Not implemented (returns error) |
| `unlink` | Not implemented (returns error) |
| `rename` | Not implemented (returns error) |
| `close` | Working |

Key limitations:
- **Read-only**: no cluster allocation, no FAT chain write-back, no directory entry creation
- **No LFN support**: only 8.3 filenames (long filename entries are skipped)
- **No write-back cache**: every read goes through BlockDevice.read_sector()
- Needs a real `BlockDevice` implementation (VirtIO block driver)

### VFS (`src/os/services/vfs/vfs.spl`)

**Status: Routing layer complete**

- `VfsManager`: multiplexes file operations across mounted filesystems
- Mount table with longest-prefix matching (`/mnt/usb` beats `/mnt`)
- File descriptor allocation (starts at fd 3, reserving 0/1/2 for stdio)
- Operations: `open`, `stat`, `readdir`, `mkdir` -- all route to mounted `Filesystem` trait impl
- Path prefix stripping for filesystem-relative paths

### What's Needed for End-to-End FS
1. **VirtIO block driver** implementing `BlockDevice` trait
2. **FAT32 write support**: cluster allocation in FAT table, directory entry creation
3. **LFN support**: parse long filename directory entries
4. **Disk image**: QEMU `-drive file=disk.img,format=raw` with FAT32 partition
5. **Wire VFS into kernel**: mount FAT32 at `/` during boot

---

## 4. Browser Status

**Status: Entity/type definitions complete, no runtime implementation**

The browser project (`examples/browser/entity/`) defines comprehensive type hierarchies across 27 files in 6 domains:

| Domain | Files | Key Types |
|--------|-------|-----------|
| **DOM** | 6 | `NodeType`, `ElementNode`, `TextNode`, `Attribute`, `EventType`, `EventPhase`, `BoxType`, `CssValue`, `PaintCommand` |
| **Net** | 6 | `Url`, `HttpMethod`, `HttpRequest`, `HttpResponse`, `Cookie`, `CacheEntry`, `CorsMode`, `TlsVersion`, `TlsCipherSuite` |
| **Browser** | 5 | `Tab`, `TabState`, `NavigationEntry`, `BrowserWindow`, `Permission`, `StorageArea` |
| **Script** | 4 | `JsValue`, `JsType`, `GcObject`, `GcState`, `AstNode`, `BytecodeOp` |
| **IPC** | 3 | `ProcessType`, `ChannelEndpoint`, `IpcMessage` |
| **Media** | 3 | `FontFace`, `FontStyle`, `ImageFormat`, `DecodedImage`, `CanvasContext` |

### What Exists
- Full entity model for a Chromium-class multi-process browser
- Multi-process architecture types (browser, renderer, GPU, network processes)
- JS engine types (AST, bytecode, GC)
- CSS box model and paint command types
- TLS/CORS/cookie security types

### What's Needed for End-to-End Browser
1. **HTML parser**: tokenizer + tree builder producing DOM tree
2. **CSS parser + style resolver**: cascade, specificity, computed styles
3. **Layout engine**: box generation, flow layout, flexbox
4. **Paint + rasterizer**: paint commands to pixel buffer
5. **JS engine runtime**: bytecode interpreter, GC, DOM bindings
6. **Network stack**: TCP/IP over VirtIO net (see below)
7. **IPC**: cross-process message passing for multi-process model
8. **Integration with compositor**: browser window as a compositor surface

---

## 5. Networking Status

### VirtIO Network Driver (`src/os/drivers/virtio/virtio_net.spl`)

**Status: Frame-level send/receive implemented**

| Operation | Status |
|-----------|--------|
| `init` | Working -- VirtIO device init, MAC address read |
| `send_frame` | Working -- VirtIO header + raw Ethernet frame via TX queue |
| `recv_frame` | Working -- non-blocking poll from RX used ring |
| `link_up` | Working -- reads link status register |
| `get_mac` | Working |

### What's Needed for End-to-End Networking
1. **TCP/IP stack**: ARP, IPv4, ICMP, UDP, TCP (no implementation exists yet)
2. **DNS resolver**: hostname to IP resolution
3. **Socket API**: BSD-style or Simple-native socket abstraction
4. **HTTP client**: HTTP/1.1 request/response on top of TCP
5. **TLS**: TLS 1.2/1.3 for HTTPS (types defined in browser entity, no runtime)
6. **Wire VirtIO net into network service**: the driver exists but no service layer connects it to applications

---

## 6. Summary: End-to-End Readiness

| Subsystem | Readiness | Blocking Items |
|-----------|-----------|----------------|
| Boot (x86_64) | 80% | Needs QEMU test with Limine ISO |
| GUI/Compositor | 70% | Needs timer interrupt, QEMU framebuffer test |
| Keyboard/Mouse | 90% | Needs real PS/2 hardware validation |
| Desktop Shell | 60% | Needs clock timer, window restore from taskbar |
| FAT32 FS | 40% | No write support, needs VirtIO block driver |
| VFS | 50% | Needs FAT32 wired in, stdio integration |
| VirtIO Net | 30% | No TCP/IP stack, no socket API |
| Browser | 10% | Types only, all runtime components missing |

### Recommended Next Steps (priority order)
1. **QEMU boot test**: build `gui_entry.spl` for x86_64, boot with Limine, verify framebuffer + compositor
2. **Timer interrupt**: PIT or APIC timer for clock updates and frame pacing
3. **VirtIO block driver**: implement `BlockDevice` trait for disk I/O
4. **FAT32 write support**: cluster allocation + directory entry creation
5. **TCP/IP stack**: ARP + IPv4 + TCP minimum for HTTP
6. **HTML parser**: first browser milestone
