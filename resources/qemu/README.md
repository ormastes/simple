# QEMU Build-from-Source Guide

This directory contains resources for building QEMU from source and managing OS images for bare-metal testing.

## Quick Start

### 1. Download QEMU Source

```bash
simple run script/download_qemu.spl
```

This downloads QEMU 8.2.0 (recommended stable version) to `resources/qemu/downloads/`.

### 2. Build QEMU

```bash
simple run script/build_qemu.spl
```

This builds QEMU with all 6 architectures:
- i386 (x86 32-bit)
- x86_64 (x86 64-bit)
- arm (ARM 32-bit / Cortex-M)
- aarch64 (ARM 64-bit / AArch64)
- riscv32 (RISC-V 32-bit)
- riscv64 (RISC-V 64-bit)

Build time: 15-30 minutes (depending on CPU)

### 3. Use Built QEMU

```bash
# Add to PATH
export PATH="$(pwd)/resources/qemu/bin:$PATH"

# Verify installation
qemu-system-x86_64 --version

# Run a kernel
qemu-system-x86_64 -kernel examples/baremetal/hello_x86.elf -nographic
```

## Directory Structure

```
resources/qemu/
├── catalog.sdn          # QEMU version catalog
├── downloads/           # Downloaded source tarballs
│   └── qemu-8.2.0.tar.xz
├── build/               # Build directory
│   └── qemu-8.2.0/      # Extracted source
├── install/             # Install directory
│   └── 8.2.0/
│       └── bin/         # Built binaries
└── bin/                 # Symlinks to active version
    ├── qemu-system-i386
    ├── qemu-system-x86_64
    ├── qemu-system-arm
    ├── qemu-system-aarch64
    ├── qemu-system-riscv32
    └── qemu-system-riscv64
```

## Build Dependencies

### Ubuntu/Debian

```bash
sudo apt install build-essential ninja-build python3 \
    pkg-config libglib2.0-dev libpixman-1-dev \
    zlib1g-dev libslirp-dev
```

### macOS

```bash
brew install ninja python@3.11 glib pixman pkg-config
```

### Windows (MSYS2)

```bash
pacman -S mingw-w64-x86_64-ninja \
    mingw-w64-x86_64-python \
    mingw-w64-x86_64-glib2 \
    mingw-w64-x86_64-pixman \
    mingw-w64-x86_64-pkg-config
```

## Available QEMU Versions

See `catalog.sdn` for full list. Stable versions:

- **8.2.0** (recommended) - Released 2023-12-19
- 8.1.5 - Released 2023-11-30
- 8.0.5 - Released 2023-09-21
- 7.2.8 - Released 2023-12-13

## Downloading OS Images

```bash
simple run script/download_images.spl
```

This downloads minimal OS images for testing:
- Alpine Linux (170 MB, minimal)
- Debian netinst (650 MB)
- Ubuntu Server (1.8 GB)

Images are saved to `resources/images/linux/`.

## Using OS Images with QEMU

```bash
# Boot Alpine Linux x86_64
qemu-system-x86_64 \
    -cdrom resources/images/linux/alpine-3.19-x86_64.iso \
    -m 2048 \
    -boot d

# Boot Debian ARM64
qemu-system-aarch64 \
    -M virt \
    -cpu cortex-a57 \
    -m 2048 \
    -cdrom resources/images/linux/debian-12-arm64-netinst.iso \
    -boot d
```

## Troubleshooting

### Build Fails: Missing Dependencies

Run the dependency check:
```bash
simple run script/build_qemu.spl
```

The script will list all missing dependencies.

### Download Fails: Network Issues

Resume the download:
```bash
# curl automatically resumes with -C -
simple run script/download_qemu.spl
```

### Checksum Mismatch

Re-download the tarball:
```bash
rm resources/qemu/downloads/qemu-8.2.0.tar.xz
simple run script/download_qemu.spl
```

### Build Hangs

Check available CPU cores:
```bash
nproc  # Linux
sysctl -n hw.ncpu  # macOS
```

The build script uses all available cores by default.

## Advanced Usage

### Build Specific Architectures Only

Edit `script/build_qemu.spl` and modify `DEFAULT_ARCHS`:

```simple
val DEFAULT_ARCHS = ["x86_64", "riscv32"]  # Only build these
```

### Use Different QEMU Version

Edit `script/build_qemu.spl` and change `QEMU_VERSION`:

```simple
val QEMU_VERSION = "8.1.5"
```

Then download and build:
```bash
simple run script/download_qemu.spl
simple run script/build_qemu.spl
```

### Clean Build

```bash
rm -rf resources/qemu/build/qemu-8.2.0
rm -rf resources/qemu/install/8.2.0
simple run script/build_qemu.spl
```

## Integration with Tests

The QEMU library automatically detects built QEMU binaries:

```simple
use src.lib.qemu.mod.{QemuArch, is_qemu_available}

# Check if QEMU is available
if is_qemu_available(QemuArch.X86_64):
    print "QEMU x86_64 found!"
```

By default, it searches:
1. `resources/qemu/bin/` (built from source)
2. System PATH (installed QEMU)

## Performance

**Build Time:**
- 4 cores: ~25 minutes
- 8 cores: ~15 minutes
- 16 cores: ~10 minutes

**Disk Usage:**
- Source tarball: 120 MB
- Extracted source: 500 MB
- Build artifacts: 1.5 GB
- Installed binaries: 200 MB
- **Total:** ~2.3 GB

**Runtime:**
- Same performance as system QEMU
- No overhead from building from source

## Benefits

1. **Version Control** - Pin exact QEMU version
2. **Reproducibility** - Same build everywhere
3. **Self-Contained** - No system dependencies
4. **Offline Capable** - Pre-download sources
5. **CI/CD Ready** - Consistent builds in CI

## References

- QEMU Official: https://www.qemu.org/
- QEMU Downloads: https://download.qemu.org/
- QEMU Documentation: https://www.qemu.org/docs/master/
- Building QEMU: https://wiki.qemu.org/Hosts/Linux

## License

QEMU is licensed under GPL v2. See QEMU source for details.
