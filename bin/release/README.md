# Release Binaries - Multi-Platform

Pre-built Simple compiler binaries, one per target triple.

## Directory Structure

Uses `<arch>-<vendor>-<os>-<abi>` target triples (matches `TargetPreset` and `LlvmTargetTriple`):

```
bin/release/
├── x86_64-unknown-linux-gnu/simple           # Linux x86_64 (ELF, GNU libc)
├── aarch64-unknown-linux-gnu/simple          # Linux ARM64 (ELF, GNU libc)
├── riscv64-unknown-linux-gnu/simple          # Linux RISC-V 64 (ELF, GNU libc)
├── x86_64-apple-darwin-macho/simple          # macOS Intel (Mach-O)
├── aarch64-apple-darwin-macho/simple         # macOS Apple Silicon (Mach-O)
├── x86_64-pc-windows-msvc/simple.exe         # Windows x86_64 MSVC (PE/COFF)
├── x86_64-pc-windows-gnu/simple.exe          # Windows x86_64 MinGW (PE/COFF)
├── aarch64-pc-windows-msvc/simple.exe        # Windows ARM64 MSVC (PE/COFF)
└── x86_64-unknown-freebsd-elf/simple         # FreeBSD x86_64 (ELF)
```

## Triple Format

```
<arch>-<vendor>-<os>-<abi>
  │       │       │     └─ ABI / object format (gnu, msvc, elf, macho)
  │       │       └─ Operating system (linux, windows, darwin, freebsd)
  │       └─ Vendor (pc, unknown, apple)
  └─ CPU architecture (x86_64, aarch64, i686, riscv64)
```

## Platform Support

| Triple | Status |
|--------|--------|
| `x86_64-unknown-linux-gnu` | Active |
| `aarch64-unknown-linux-gnu` | Builds |
| `riscv64-unknown-linux-gnu` | Experimental |
| `x86_64-apple-darwin-macho` | Prepared |
| `aarch64-apple-darwin-macho` | Prepared |
| `x86_64-pc-windows-msvc` | Builds |
| `x86_64-pc-windows-gnu` | Prepared |
| `aarch64-pc-windows-msvc` | Experimental |
| `x86_64-unknown-freebsd-elf` | Prepared |

## Setup

After cloning or bootstrapping, run setup to create the `bin/simple` symlink:

```bash
# Linux / macOS / Git Bash
scripts/setup.sh

# Windows CMD / PowerShell
scripts\setup.cmd
```

This creates `bin/simple(.exe)` pointing to the correct `bin/release/<triple>/simple(.exe)`.

## Direct Execution

```bash
# Linux x86_64
bin/release/x86_64-unknown-linux-gnu/simple your_script.spl

# macOS ARM64
bin/release/aarch64-apple-darwin-macho/simple your_script.spl

# Windows x86_64 MSVC
bin\release\x86_64-pc-windows-msvc\simple.exe your_script.spl
```

## Building

```bash
# Bootstrap from source (Linux)
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
scripts/setup.sh

# Bootstrap from source (Windows)
scripts/bootstrap/bootstrap-windows.sh --deploy
scripts/setup.sh
```

## Binary Characteristics

- **Format**: Native executable (ELF, Mach-O, or PE per platform)
- **Linking**: Dynamically linked (requires system libc)
- **Size**: ~22-64 MB (release build, varies by backend)
- **Debug Info**: Stripped for release

## Gitignore

All binaries under `bin/release/` are git-ignored. Only this `README.md` is tracked.
After cloning, either download pre-built binaries or bootstrap from source, then run `scripts/setup.sh`.
