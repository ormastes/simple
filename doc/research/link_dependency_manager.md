# Link Dependency Manager — Research

## Cross-References
- Requirement: `doc/requirement/link_dependency_manager.md`
- Plan: `doc/plan/link_dependency_manager.md`

## 1. Current State Analysis

### Hardcoded Dependencies (6 files)

| File | What's Hardcoded | Lines |
|------|-----------------|-------|
| `linker_wrapper.spl` | `-lc -lpthread -ldl -lm` (Linux), `-lc -lpthread -lm -lSystem` (macOS) | 206-220, 424-428 |
| `mold.spl` | `-lc -lpthread -ldl -lm` | 435-439 |
| `msvc.spl` | `kernel32.lib user32.lib` | 29 |
| `crt_discovery.spl` | CRT paths for x86_64/aarch64/riscv64, dynamic linker paths, GCC lib paths | 26-33, 133-147, 213 |
| `linker_wrapper_lib_support.spl` | `/usr/lib/simple`, `/usr/local/lib/simple` | 28 |
| `linker_wrapper.spl` | Simple runtime lib dir | 369 |

### Current Discovery Flow
1. CRT: filesystem probe → hardcoded arch-specific paths
2. Dynamic linker: hardcoded paths → `readelf -l /bin/sh` fallback
3. GCC runtime: `gcc -print-file-name=` → probe versions 14-9
4. System libs: hardcoded per OS (no discovery)
5. Linker: mold → lld → ld → cc (preference chain)

### Existing Infrastructure
- **ProjectContext** (`80.driver/project.spl`): loads `simple.sdn`, already supports features/profiles
- **IncrementalBuild** (`80.driver/build/incremental.spl`): dependency tracking with SHA256 hashing
- **SDN parser**: supports nested sections, arrays, key-value pairs

## 2. How Other Languages Handle This

### Rust (Cargo + build.rs)
- **Manifest**: `Cargo.toml` has `[package]` with `links = "foo"` key
- **Build script**: `build.rs` runs at compile time, prints `cargo:rustc-link-lib=foo`
- **pkg-config**: `pkg_config::Config::new().probe("libname")` auto-detects flags
- **Platform conditionals**: `#[cfg(target_os = "linux")]` in build.rs
- **Strengths**: Full programmability via build scripts
- **Weaknesses**: Complex, requires Rust code for native deps

### Python (setuptools)
- **Manifest**: `setup.py` with `Extension(libraries=["foo"], library_dirs=[...])`
- **Platform**: Source distributions; users compile on their platform
- **Strengths**: Simple declarative API for extensions
- **Weaknesses**: No automatic discovery, manual per-platform config

### Node.js (node-gyp)
- **Manifest**: `binding.gyp` with `targets[].libraries` array
- **Platform**: `conditions` blocks for os-specific flags
- **Strengths**: Platform conditions in same file
- **Weaknesses**: GYP format is verbose and niche

### Common Patterns
All three share: **declarative manifest + platform conditionals + `-l`/`-L` flag generation**

## 3. Recommended Approach for Simple

### Design: Declarative SDN + Platform Defaults Module

**Layer 1 — Platform defaults** (single `.spl` file):
```simple
# src/compiler/70.backend/linker/platform_defaults.spl
fn default_link_config(os: text, arch: text) -> LinkConfig:
    match os:
        "linux": LinkConfig(
            libraries: ["c", "pthread", "dl", "m"],
            crt_search_paths: crt_paths_for(arch),
            dynamic_linker: dynamic_linker_for(arch)
        )
        "macos": LinkConfig(
            libraries: ["c", "pthread", "m", "System"],
            ...
        )
        "windows": LinkConfig(
            libraries: ["kernel32", "user32"],
            ...
        )
```

**Layer 2 — Project manifest** (`simple.sdn`):
```sdn
[links]
libraries: ["GL", "X11"]

[links.linux]
library_dirs: ["/usr/lib/x86_64-linux-gnu"]

[links.windows]
libraries: ["opengl32"]
```

**Layer 3 — Merge** at build time:
```
final_config = platform_defaults(os, arch)
    .merge(project_links)
    .merge(project_links[os])
    .merge(project_links[os][arch])
```

### Why This Design
1. **Single source of truth** for defaults (not scattered across 6 files)
2. **No build scripts needed** — declarative SDN is sufficient for most cases
3. **Compatible with bootstrap** — defaults module is just a Simple function
4. **Rust bootstrap** can read same `simple.sdn` or hardcode same defaults
5. **Incremental migration** — replace hardcoded values one file at a time

### Migration Strategy
1. Create `platform_defaults.spl` with all current hardcoded values
2. Extend `ProjectContext` to parse `[links]` from `simple.sdn`
3. Create `LinkConfig` merge logic
4. Create `check-links` CLI command
5. Replace hardcoded libs in `linker_wrapper.spl` → read from config
6. Replace hardcoded libs in `mold.spl` → read from config
7. Replace hardcoded libs in `msvc.spl` → read from config
8. Extract CRT paths from `crt_discovery.spl` → platform_defaults
9. Test Rust bootstrap still works
10. Full bootstrap cycle

### Risk: Bootstrap Chicken-and-Egg
- **Problem**: If platform_defaults.spl uses fancy features, the bootstrap compiler might not support them
- **Mitigation**: Keep platform_defaults.spl using only basic language features (match, arrays, text)
- **Fallback**: Rust bootstrap can hardcode the same defaults independently

### Windows Considerations
- Library paths: `C:\Program Files (x86)\Windows Kits\10\Lib\...`
- SDK discovery: Read `HKLM\SOFTWARE\Microsoft\Windows Kits` registry or use `vswhere.exe`
- MSVC: `cl.exe` and `link.exe` paths from Visual Studio installation
- Alternative: Use environment from "Developer Command Prompt" (vcvarsall.bat sets PATH/LIB/INCLUDE)
