# Dynamic Library API Guide

## Overview

SimpleOS provides a unified dynamic library loading API through the `DynLibKind`
enum, which dispatches to ELF, SMF, and PE backends. The SFFI bridge
(`dynlib_sffi`) enables calling functions in loaded libraries by name.

## Architecture

```
dynlib.spl          -- OOP enum dispatch (DynLibKind)
dynlib_sffi.spl     -- rt_dyncall externs + safe wrappers
dylib_async.spl     -- async-first kernel backend
dylib_registry.spl  -- kernel handle table (ELF/SMF)
```

## Quick Start

```spl
use os.posix.dynlib.{dynlib_open, dynlib_symbol, dynlib_close, dynlib_is_valid}
use os.posix.dynlib_sffi.{dynlib_call_1}

# Open a shared library
val lib = dynlib_open("/lib/libmath.so", 0)
if dynlib_is_valid(lib):
    # Call a function by name
    val result = dynlib_call_1(lib, "compute", 42)
    dynlib_close(lib)
```

## DynLibKind Enum

| Variant | Extension | Backend | Status |
|---------|-----------|---------|--------|
| `Elf`   | `.so`     | Kernel dylib_registry | Wired (pre-registered libraries) |
| `Smf`   | `.smf`    | Kernel dylib_registry | Wired (pre-registered libraries) |
| `Pe`    | `.dll`    | Wine PE loader | Implemented (image mapping + relocations) |
| `Invalid` | — | — | Error sentinel |

## API Reference

### dynlib.spl

- `dynlib_open(path: text, mode: u32) -> DynLibKind` — open by extension sniffing
- `dynlib_symbol(lib: DynLibKind, name: text) -> i64` — resolve named symbol
- `dynlib_close(lib: DynLibKind) -> i64` — close and release handle
- `dynlib_is_valid(lib: DynLibKind) -> bool` — check if loaded successfully
- `dynlib_path(lib: DynLibKind) -> text` — get filesystem path
- `dynlib_format_name(lib: DynLibKind) -> text` — human-readable format name

### dynlib_sffi.spl

- `dynlib_call_0..6(lib, name, args...) -> i64` — resolve + call with 0-6 args

## Current Limitations

- **Libraries must be pre-registered**: `dylib_async_open` calls
  `dylib_registry_open(path)`, which only finds libraries previously registered
  via `dylib_registry_register(path, bytes)`. Unregistered paths return ENOENT.
- **rt_dyncall_N not in runtime**: the extern declarations are forward contracts;
  calling them before runtime support will trap.

## Testing

```bash
bin/simple test test/unit/os/posix/dynlib_spec.spl
bin/simple test test/unit/os/posix/dylib_async_spec.spl
```
