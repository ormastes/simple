# Dynamic Loading System Tests

System-level integration tests for the dynamic library loading infrastructure.

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

## Test Matrix

| Spec | Format | Platform Gate | Tests |
|------|--------|---------------|-------|
| `dynload_linux_elf_system_spec` | ELF64 | `is_linux()` | register, open, symbol resolve, close, refcount, error handling |
| `dynload_simpleos_smf_system_spec` | SMF-wrapped ELF64 | `is_linux()` | SMF load, entry resolve, invalid stub rejection, mixed registry |
| `dynload_macos_system_spec` | ELF64 cross-load | `is_macos()` | register, symbol resolve (SKIP on non-macOS) |
| `dynload_windows_pe_system_spec` | PE64 | `is_windows()` (partial) | relocation, export lookup, image mapping, DllMain lifecycle |

## File Structure

All specs import fixture builders from a shared helpers module:

```
test/system/dynload/
  dynload_fixture_helpers.spl          # Shared ELF64/SMF/PE64 byte-array builders
  dynload_linux_elf_system_spec.spl    # Linux ELF system tests
  dynload_simpleos_smf_system_spec.spl # SimpleOS SMF system tests
  dynload_macos_system_spec.spl        # macOS cross-load tests
  dynload_windows_pe_system_spec.spl   # Windows PE system tests
  .spipe_matchers_*.spl                # SPipe matchers companions
```

## Fixture Strategy

Tests use **synthetic in-memory byte arrays** (not gcc-compiled real .so files)
because the interpreter FFI `[u8]` wrapping bug causes `file_read_bytes()` to
return `Option::Some([bytes])` instead of plain `[u8]`. Once this bug is fixed,
tests should be updated to use real compiled fixtures via `gcc -shared`.

Fixture builders are shared via `test.system.dynload.dynload_fixture_helpers`:
- `make_elf64_exec()` -- minimal valid ELF64 ET_EXEC with entry 0x400000
- `make_elf64_with_dynsym()` -- ELF64 with .dynsym containing "hello" at 0xBEEF
- `make_smf_wrapped_elf64_exec()` -- SMF container wrapping ELF64 as native stub
- `make_pe64_reloc_image()` -- PE64 with relocation directory
- `make_pe64_export_image()` -- PE64 with export directory (Alpha, Beta exports)

## Platform Gating

No formal `skip_if()` mechanism exists in the test runner. Platform-specific
tests use inline `if is_linux():` / `if is_macos():` / `if is_windows():` guards
from `std.env.platform`. On non-matching platforms, tests print a SKIP message
and pass without assertion.

## Interpreter Mode Limitation

Tests run in interpreter mode (file-loading + `it` block execution). The test
runner verifies both file loading and assertion execution. Full compiled-mode
(`--mode=native` / `--mode=smf`) verification is deferred until R2-broader lands
because those modes can produce false-greens via stub-generation or swallowed errors.

## Covered Modules

- `src/os/kernel/loader/dylib_registry.spl` -- register, open, symbol, close, reset
- `src/os/kernel/loader/elf64.spl` -- ELF64 header/section parsing
- `src/os/kernel/loader/smf.spl` -- SMF header detection, stub extraction
- `src/lib/common/pe_coff_header.spl` -- PE export lookup, image base/size
- `src/lib/common/wine_pe_loader_runtime.spl` -- PE relocation application
- `src/lib/common/wine_dll_image_loader.spl` -- PE image mapping
- `src/lib/common/wine_dll_entrypoint_lifecycle.spl` -- DllMain lifecycle
