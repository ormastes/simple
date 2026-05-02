# External Native Libraries

Canonical guide for integrating optional third-party native libraries with
Simple.

## Scope

Use this pattern when you want a Simple program to consume a host library such
as zlib, SQLite, OpenCV, or a vendor SDK without making that library part of
the compiler/runtime default native link set.

The canonical example lives at:

- `examples/10_tooling/libraries/external_compression/`

## Recommended Architecture

1. Build a thin C ABI bridge around the third-party library.
2. Let CMake or the bridge build own package discovery and link flags.
3. Export a minimal symbol surface with stable `extern "C"` functions.
4. Load that bridge explicitly from Simple with `spl_dlopen`.

This keeps optional dependencies separate from core compiler/runtime
dependencies such as `simple_runtime` and `simple_native_all`.

## Build Ownership

The bridge project, not `bin/simple compile`, should resolve external package
details:

- system package lookup (`find_package`, pkg-config, custom paths)
- checkout/fetch of upstream source
- `target_link_libraries(...)`
- platform-specific rpath or DLL placement

Today, `simple compile --native` intentionally does not expose a general-purpose
`-l`/`-L` pass-through API for arbitrary external host libraries. The supported
and stable route is:

- compile the Simple side normally
- load the optional bridge at runtime

## Simple Discovery Model

The Simple program should resolve the bridge path explicitly:

1. dedicated env var such as `SIMPLE_ZLIB_BRIDGE_PATH`
2. known generated build outputs
3. app-local install location if you provide one

If no candidate exists, fail with a clear diagnostic. Do not silently fall back
to compiler/runtime default libraries.

## Binding Shape

Use the existing runtime loading primitives:

```simple
extern fn spl_dlopen(path: text) -> i64
extern fn spl_dlsym(handle: i64, name: text) -> i64
extern fn spl_wffi_call_i64(fptr: i64, args: [i64], nargs: i64) -> i64
extern fn rt_string_data(s: text) -> i64
extern fn rt_cstring_to_text(ptr: i64) -> text
```

Guidelines:

- prefer simple C ABI functions over exposing C++ directly
- prefer `(ptr, len)` inputs for text or byte payloads when the callee does not
  need a nul-terminated C string
- prefer explicit `*_free` functions for bridge-owned strings or buffers
- keep the function surface minimal and task-focused
- surface a `*_last_error()` accessor for diagnostics

## Optional Dependency Policy

Optional external libraries must not be added to the compiler/runtime native
default link set unless they are required for every normal native executable.

That means:

- `simple_runtime` and `simple_native_all` are core dependencies
- zlib, liblzma, torch, vendor SDKs, and similar packages are optional unless a
  specific feature lane says otherwise

If a feature requires an external package, gate it to that feature's bridge or
build lane and document the requirement there.

## Canonical Compression Example

The external compression example demonstrates:

- `FetchContent` or system-package zlib acquisition
- explicit `target_link_libraries(simple_zlib_bridge PRIVATE ...)`
- `simple_zlib_compress_bytes_to_hex`
- `simple_zlib_decompress_hex_bytes`
- `simple_zlib_roundtrip_selftest`
- `simple_zlib_last_error`
- explicit missing-library behavior from the Simple side

## Related Docs

- `doc/07_guide/ffi/sffi.md`
- `doc/05_design/sffi_bidirectional_interop.md`
- `doc/05_design/sffi_external_library_pattern.md`
