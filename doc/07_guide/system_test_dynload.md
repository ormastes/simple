# Dynamic Loading System Tests Guide

## Overview

System-level integration tests for SimpleOS dynamic library loading. Tests
exercise the full pipeline: build fixture -> register -> open -> resolve
symbol -> close. Covers ELF (.so), SMF (.smf), and PE (.dll) formats.

## Test Files

| File | Platform | What it tests |
|------|----------|---------------|
| `dynload_linux_elf_system_spec.spl` | All (Linux-focused) | ELF64 register/open/symbol/close via dylib_registry |
| `dynload_simpleos_smf_system_spec.spl` | All | SMF-wrapped ELF loading via dylib_registry |
| `dynload_macos_system_spec.spl` | macOS (skips elsewhere) | ELF cross-load verification on macOS |
| `dynload_windows_pe_system_spec.spl` | All | PE64 relocation, export lookup, image mapping |

## Running

```bash
# All dynload system tests
bin/simple test test/system/dynload/

# Individual specs
bin/simple test test/system/dynload/dynload_linux_elf_system_spec.spl
bin/simple test test/system/dynload/dynload_simpleos_smf_system_spec.spl
bin/simple test test/system/dynload/dynload_macos_system_spec.spl
bin/simple test test/system/dynload/dynload_windows_pe_system_spec.spl
```

## Fixture Strategy

Tests use **synthetic byte-array fixtures** built in-memory, not gcc-compiled
binaries. This avoids:
- Toolchain dependency (no gcc/clang required)
- Interpreter FFI `[u8]` wrapping bug with `file_read_bytes`
- Platform-specific binary format issues

Fixture builders construct valid ELF64, SMF, and PE64 images byte-by-byte
using `push_u16_le`/`push_u32_le`/`push_u64_le` helpers, matching the
patterns in the unit test specs.

## Platform Gating

No formal `skip_if()` mechanism exists in the test runner. Platform-specific
tests use inline `if is_macos():` / `if is_windows():` guards from
`std.env.platform`. On non-matching platforms, tests print a SKIP message
and pass with a trivial assertion.

```spl
use std.env.platform.{is_macos}

it "does something macOS-specific":
    if is_macos():
        # actual test
    else:
        print("SKIP: not on macOS")
        expect(true).to_equal(true)
```

## Interpreter Mode Limitation

The test runner in interpreter mode verifies file loading and basic parsing
but may not execute all `it` block assertions. Tests are structured to be
lint-clean and load without errors. Full assertion-level verification
requires compiled mode (future work).

## Architecture

```
test/system/dynload/
  dynload_linux_elf_system_spec.spl       # ELF: register + open + symbol + close
  dynload_simpleos_smf_system_spec.spl    # SMF: unwrap ELF stub + registry
  dynload_macos_system_spec.spl           # ELF cross-load (macOS-gated)
  dynload_windows_pe_system_spec.spl      # PE: relocation + export + mapping

src/os/kernel/loader/
  dylib_registry.spl     # Handle table (register/open/symbol/close)
  elf64.spl              # ELF64 parser (.dynsym, section headers)
  smf.spl                # SMF container parser

src/os/posix/
  dylib_async.spl        # Async request API (kernel backend)
  dynlib.spl             # OOP DynLibKind enum dispatch

src/lib/common/
  pe_coff_header.spl             # PE parser (exports, imports)
  wine_pe_loader_runtime.spl     # PE relocation walker
  wine_dll_image_loader.spl      # PE image mapping
  wine_dll_entrypoint_lifecycle.spl  # DllMain gate
```
