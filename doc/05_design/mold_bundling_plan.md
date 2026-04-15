# Mold Bundling Plan

## Overview

Bundle the mold linker with Simple for seamless native binary generation.

**License**: MIT (since mold 2.0) - **Safe to bundle and distribute**

## Options

### Option 1: Bundle Pre-built Binaries (Recommended)

Download and bundle pre-built mold binaries for each platform.

```
simple/
├── bin/
│   ├── mold-linux-x86_64      # Linux x86_64
│   ├── mold-linux-aarch64     # Linux ARM64
│   ├── mold-macos-x86_64      # macOS Intel
│   └── mold-macos-aarch64     # macOS Apple Silicon
```

**Pros:**
- No build dependency
- Fast installation
- Works offline

**Cons:**
- Larger package size (~20MB per platform)
- Need to update when mold releases new versions

### Option 2: Auto-Download on First Use

Download mold binary on first use of `simple build --native`.

```simple
fn ensure_mold() -> Result<text, text>:
    val mold_path = get_mold_cache_path()
    if not file_exists(mold_path):
        download_mold(mold_path)?
    Ok(mold_path)
```

**Pros:**
- Smaller initial package
- Always latest version

**Cons:**
- Requires internet on first use
- Download may fail

### Option 3: System Detection with Fallback

1. Check for system mold/lld/ld
2. If not found, use bundled or download

```simple
fn find_linker() -> Result<(text, LinkerType), text>:
    # 1. Check bundled mold
    val bundled = get_bundled_mold_path()
    if file_exists(bundled):
        return Ok((bundled, LinkerType.Mold))

    # 2. Check system mold
    if which("mold").?:
        return Ok((which("mold").unwrap(), LinkerType.Mold))

    # 3. Fallback to lld
    if which("ld.lld").?:
        return Ok((which("ld.lld").unwrap(), LinkerType.Lld))

    # 4. Fallback to system ld
    if which("ld").?:
        return Ok((which("ld").unwrap(), LinkerType.Ld))

    Err("No linker found")
```

## Recommended Approach: Option 3 (Hybrid)

1. **Bundle mold** in release packages for common platforms
2. **Detect system mold** first (user may have newer version)
3. **Fallback chain**: bundled mold → system mold → lld → ld

## Implementation Plan

### Phase 1: Download Script

```bash
# scripts/download-mold.sh
MOLD_VERSION="2.34.0"
PLATFORM=$(uname -s)-$(uname -m)

case $PLATFORM in
    Linux-x86_64)
        URL="https://github.com/rui314/mold/releases/download/v${MOLD_VERSION}/mold-${MOLD_VERSION}-x86_64-linux.tar.gz"
        ;;
    Linux-aarch64)
        URL="https://github.com/rui314/mold/releases/download/v${MOLD_VERSION}/mold-${MOLD_VERSION}-aarch64-linux.tar.gz"
        ;;
    Darwin-x86_64|Darwin-arm64)
        # macOS - use Homebrew or build from source
        ;;
esac

curl -L "$URL" | tar xz -C bin/
```

### Phase 2: Rust FFI for Linker Detection

```rust
// src/rust/compiler/src/linker/mold_ffi.rs

use std::process::Command;
use std::path::PathBuf;

/// Find mold binary, checking bundled first
#[no_mangle]
pub extern "C" fn mold_find_path() -> *const c_char {
    // 1. Check bundled
    let bundled = get_bundled_path();
    if bundled.exists() {
        return to_c_string(bundled);
    }

    // 2. Check PATH
    if let Ok(output) = Command::new("which").arg("mold").output() {
        if output.status.success() {
            return to_c_string(String::from_utf8_lossy(&output.stdout).trim());
        }
    }

    std::ptr::null()
}

fn get_bundled_path() -> PathBuf {
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|p| p.to_path_buf()))
        .unwrap_or_default();

    exe_dir.join("mold")
}
```

### Phase 3: Update mold.spl

Already implemented - just needs the FFI backend.

### Phase 4: Release Packaging

```yaml
# .github/workflows/release.yml
jobs:
  build:
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
            mold: mold-2.34.0-x86_64-linux
          - os: ubuntu-latest
            target: aarch64-unknown-linux-gnu
            mold: mold-2.34.0-aarch64-linux

    steps:
      - name: Download mold
        run: |
          curl -L "https://github.com/rui314/mold/releases/download/v2.34.0/${{ matrix.mold }}.tar.gz" | tar xz
          mv mold-*/bin/mold target/release/
```

## License Compliance

Include in distribution:

```
third-party/mold/LICENSE
---
MIT License

Copyright (c) 2020-2024 Rui Ueyama

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software...
```

## Size Estimates

| Platform | Mold Binary Size |
|----------|------------------|
| Linux x86_64 | ~18MB |
| Linux aarch64 | ~16MB |
| macOS | ~15MB |

Total package increase: ~20MB per platform (compressed: ~5MB)

## Timeline

| Phase | Task | Duration |
|-------|------|----------|
| 1 | Download script | 1 day |
| 2 | Rust FFI | 2 days |
| 3 | Update mold.spl | Done |
| 4 | Release packaging | 2 days |
| 5 | Testing | 2 days |

**Total: ~1 week**

## References

- [Mold GitHub](https://github.com/rui314/mold)
- [Mold 2.0 MIT License Announcement](https://www.phoronix.com/news/Mold-2.0-Linker)
- [Mold Releases](https://github.com/rui314/mold/releases)
