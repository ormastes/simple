# Link Dependency Manager — Requirements

## Feature Name
**Link Dependency Manager** — Extract hardcoded system library links into a declarative, platform-aware dependency tracking system managed by the package/import manager.

## Motivation (Why)
Currently, system library dependencies (`-lc`, `-lpthread`, `-ldl`, `-lm`, CRT paths, dynamic linker paths) are **hardcoded** across multiple linker files:
- `linker_wrapper.spl` (lines 206-220, 424-428)
- `mold.spl` (lines 435-439)
- `msvc.spl` (line 29)
- `crt_discovery.spl` (lines 26-33, 133-147, 213)

This causes:
1. **Fragility** — Adding a new platform requires editing multiple files
2. **No user control** — Users cannot add/remove system libraries for their project
3. **No dependency tracking** — The compiler doesn't know *why* a library is needed
4. **Bootstrap coupling** — Rust bootstrap and pure Simple must duplicate linker knowledge
5. **Windows gaps** — Windows platform paths are incomplete

## Scope

### In Scope
1. **Declarative link dependency specification** in `simple.sdn` project manifest
2. **Platform-conditional dependencies** (linux/macos/freebsd/windows × arch)
3. **System library discovery** via filesystem probing + fallback
4. **CRT and dynamic linker path abstraction** into discovery modules
5. **Default link set** per platform (so projects work without explicit config)
6. **Both Rust bootstrap and pure Simple** implementations
7. **Incremental migration** — remove hardcoded links one by one, test each
8. **Re-bootstrap** after changes to verify self-hosting

### Out of Scope
- Package registry / remote package downloads (future feature)
- Automatic dependency inference from source imports (future feature)
- Version constraint solving (future feature)

## I/O Examples

### Example 1: Default project (no explicit link config)
```sdn
# simple.sdn — minimal project
name: "myapp"
version: "0.1.0"
# No [links] section → compiler uses platform defaults
```
**Result:** Links `-lc -lpthread -lm` on Linux, `-lc -lpthread -lm -lSystem` on macOS, `kernel32.lib user32.lib` on Windows.

### Example 2: Project with extra system libraries
```sdn
name: "graphics_app"
version: "0.1.0"

[links]
libraries: ["GL", "X11", "Xrandr"]

[links.linux]
libraries: ["GL", "X11", "Xrandr"]
library_dirs: ["/usr/lib/x86_64-linux-gnu"]

[links.windows]
libraries: ["opengl32", "gdi32"]
library_dirs: ["C:\\Windows\\System32"]

[links.macos]
frameworks: ["OpenGL", "Cocoa"]
```
**Result:** Platform-specific libraries appended to defaults.

### Example 3: Project that removes a default library
```sdn
name: "embedded_app"
version: "0.1.0"

[links]
no_default_libs: true
libraries: ["c"]  # Only libc, no pthread/dl/m
```
**Result:** Only `-lc` linked.

### Example 4: Check link command
```bash
$ bin/simple check-links
Checking link dependencies for platform: linux-x86_64
  [OK] libc (-lc) ... found at /usr/lib/x86_64-linux-gnu/libc.so
  [OK] libpthread (-lpthread) ... found at /usr/lib/x86_64-linux-gnu/libpthread.so
  [OK] libm (-lm) ... found at /usr/lib/x86_64-linux-gnu/libm.so
  [OK] libdl (-ldl) ... found at /usr/lib/x86_64-linux-gnu/libdl.so
  [OK] CRT files ... found (crt1.o, crti.o, crtn.o)
  [OK] Dynamic linker ... /lib64/ld-linux-x86-64.so.2
All 6 link dependencies satisfied.
```

### Example 5: Missing library detection
```bash
$ bin/simple check-links
Checking link dependencies for platform: linux-x86_64
  [OK] libc (-lc) ... found
  [FAIL] libGL (-lGL) ... not found
    Searched: /usr/lib/x86_64-linux-gnu, /usr/lib64, /usr/local/lib
    Install: sudo apt install libgl-dev (Debian/Ubuntu)
  [OK] libm (-lm) ... found
1 link dependency missing. Build will fail at link stage.
```

## Acceptance Criteria

1. **AC-1**: `simple.sdn` supports `[links]` section with `libraries`, `library_dirs`, `no_default_libs` fields
2. **AC-2**: Platform-conditional subsections `[links.linux]`, `[links.macos]`, `[links.windows]`, `[links.freebsd]` are supported
3. **AC-3**: Architecture-conditional subsections `[links.linux.x86_64]`, `[links.linux.aarch64]` etc. are supported
4. **AC-4**: Default link set is defined per platform in a single data file, not scattered across linker code
5. **AC-5**: `bin/simple check-links` CLI command validates all link dependencies are present
6. **AC-6**: Hardcoded library lists removed from `linker_wrapper.spl`, `mold.spl`, `msvc.spl`
7. **AC-7**: Hardcoded CRT/dynamic-linker paths extracted from `crt_discovery.spl` into platform config
8. **AC-8**: Rust bootstrap (`src/compiler_rust/`) uses same dependency data or equivalent
9. **AC-9**: Full bootstrap cycle succeeds: Rust seed → Simple compiler → self-hosted binary
10. **AC-10**: Windows `check-links` works with MSVC paths (`kernel32.lib`, `user32.lib`, etc.)

## Dependencies on Existing Modules

| Module | Path | Dependency Type |
|--------|------|----------------|
| ProjectContext | `src/compiler/80.driver/project.spl` | Extend to load `[links]` section |
| LinkerWrapper | `src/compiler/70.backend/linker/linker_wrapper.spl` | Refactor to read from config |
| CRT Discovery | `src/compiler/70.backend/linker/crt_discovery.spl` | Extract paths to config |
| Mold Backend | `src/compiler/70.backend/linker/mold.spl` | Remove hardcoded libs |
| MSVC Backend | `src/compiler/70.backend/linker/msvc.spl` | Remove hardcoded libs |
| CLI Main | `src/app/cli/main.spl` | Add `check-links` command |
| SDN Parser | `src/lib/common/sdn/` | Already supports nested sections |
| Rust Driver | `src/compiler_rust/driver/src/main.rs` | Parallel Rust impl |

## Cross-References
- Research: `doc/research/link_dependency_manager.md`
- Plan: `doc/plan/link_dependency_manager.md` (Phase 4)
- System Test: `test/system/link_dependency_manager_spec.spl` (Phase 6)
