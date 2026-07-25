# Research: Cross-Platform Installation Package Generation

**Date:** 2026-03-28
**Status:** Approved for implementation

## Problem

The Simple compiler currently ships as `.spk` tarballs via GitHub Releases. Users on Ubuntu, Windows, macOS, and FreeBSD expect native installation packages (`.deb`, `.exe`, `.pkg`, `.txz`) for familiar install workflows.

## Requirements

- Generate native packages for: Ubuntu (.deb), Windows (.exe installer), macOS (.pkg), FreeBSD (.txz)
- All package generation must run from Linux (cross-platform packaging)
- Tools must be free and open-source
- Wrapper library in Simple with .shs script interface

## Tool Evaluation

### Single-Tool Candidates

| Tool | Formats | macOS | FreeBSD | Windows | Deps | License |
|------|---------|-------|---------|---------|------|---------|
| **FPM** | deb, rpm, osxpkg, freebsd, tar.gz, sh | Yes (.pkg) | Yes (.txz) | No | Ruby | MIT |
| **nFPM** | deb, rpm, apk, msix | No | No | Partial | None (Go binary) | MIT |
| **GoReleaser** | deb, rpm, msi, nsis, pkg, dmg | Yes | No | Yes | Go + plugins | MIT (Pro: paid) |
| **CPack** | deb, rpm, nsis, wix, pkg, dmg, freebsd | Yes | Yes | Yes | CMake | BSD-3 |

**Verdict:** No single free tool covers all 4 platforms adequately.

### Recommended Combination

| Tool | Covers | Runs on Linux | Install |
|------|--------|---------------|---------|
| **FPM** | .deb, .rpm, .osxpkg, .freebsd | Yes | `gem install fpm` |
| **NSIS** (makensis) | Windows .exe installer | Yes (native) | `apt install nsis` |

**Why FPM:**
- Single tool creates 4+ package formats from a directory layout
- Zero platform-specific knowledge needed - same `-s dir` input, different `-t` output
- Actively maintained, MIT licensed, widely used in industry
- Ruby is the only dependency (no Go, .NET, or Wine needed)

**Why NSIS over WiX:**
- `makensis` compiles natively on Linux (`apt install nsis`)
- WiX requires .NET/Mono on Linux (heavy dependency)
- NSIS has better Linux cross-compilation support
- Scriptable with template variable substitution

**Fallback:** `dpkg-deb` for .deb (zero external dependencies, already implemented in `build_deb.spl`)

### Rejected Options

- **WiX Toolset**: Requires .NET/Mono on Linux, complex setup
- **nFPM**: Missing macOS and FreeBSD support
- **GoReleaser**: Go dependency, some features require paid subscription
- **Inno Setup**: Windows-only (requires Wine on Linux)
- **msitools (wixl)**: Limited to .msi, less mature than NSIS

## Cross-Platform Packaging from Linux

| Target | Tool | Method |
|--------|------|--------|
| Ubuntu .deb | FPM or dpkg-deb | Native Linux |
| Fedora .rpm | FPM | Native Linux |
| macOS .pkg | FPM (`-t osxpkg`) | Creates .pkg structure on Linux |
| FreeBSD .txz | FPM (`-t freebsd`) | Creates FreeBSD pkg on Linux |
| Windows .exe | NSIS (`makensis`) | Compiles .nsi script on Linux |

**Note:** macOS .pkg created from Linux cannot be signed without macOS. Code signing is a separate CI step on macOS runners.

## Architecture Decision

- Library: `src/lib/nogc_sync_mut/package/installer/`
- CLI: `bin/simple build installer --platform=<target>`
- Scripts: `scripts/packaging/build-installers.shs`
- Config: `config/packaging/` (existing + new NSIS template)

## References

- FPM: https://fpm.readthedocs.io/
- NSIS: https://nsis.sourceforge.io/
- nFPM: https://nfpm.goreleaser.com/
- Existing deb builder: `src/compiler/80.driver/build/build_deb.spl`
- Existing dist module: `src/lib/nogc_sync_mut/package/dist.spl`
