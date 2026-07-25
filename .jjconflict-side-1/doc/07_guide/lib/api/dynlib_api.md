# Dynamic Library API Guide

## Overview

SimpleOS provides a unified dynamic library loading API through the `DynLibKind`
enum, which dispatches to ELF, SMF, and PE backends. The SFFI bridge
(`dynlib_sffi`) resolves function symbols and can call process-callable native
ABI function pointers through `rt_dyncall_0..6`.

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

# Open a pre-registered library
val lib = dynlib_open("/lib/libmath.so", 0)
if dynlib_is_valid(lib):
    # Only call when the loader evidence proves the symbol is process-callable.
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
- `dynlib_symbol_is_process_callable(lib: DynLibKind, name: text) -> bool` —
  true only when the resolved symbol is safe to call as a host-process pointer
- `dynlib_close(lib: DynLibKind) -> i64` — close and release handle
- `dynlib_is_valid(lib: DynLibKind) -> bool` — check if loaded successfully
- `dynlib_path(lib: DynLibKind) -> text` — get filesystem path
- `dynlib_format_name(lib: DynLibKind) -> text` — human-readable format name

### dynlib_sffi.spl

- `dynlib_call_0..6(lib, name, args...) -> i64` — resolve + call with 0-6 args

### smf_dynlib.spl

- `smf_dlopen(req, next_handle) -> DynLoadResult` — compatibility SMF dynlib
  facade that validates request shape and returns a session handle.
- `smf_dlopen_checked(req, next_handle) -> DynLoadResult` — fail-closed SMF
  dynlib open for generated artifacts; requires a `.smf` path, file existence,
  and `SMF\0` magic before returning a handle.
- `smf_dlsym(handle, symbol, registry) -> DynSymResult` — resolve a symbol in
  the session-owned handle registry.
- `smf_dlclose(handle) -> DynCloseResult` — validate and close a session handle.

## stdlib-like dynSMF Startup

The low-dependency UI dynSMF lane adds a startup-facing session path for the
stdlib-like libraries `file_io`, `net_io`, `render2d`, `web_renderer`,
`gui_renderer`, and `tui_renderer`.

- Manifest/session implementation: `src/os/smf/dynsmf_session.spl`
- Startup adapter: `src/app/startup/dynsmf_autoload.spl`
- Artifact build evidence: `scripts/check/check-low-dependency-dynsmf-build-plans.shs`
- App-root status: `simple run src/app/main.spl --dynsmf-status`
- Disable all default autoload: `--no-dynsmf` or `SIMPLE_DYNSMF=0`
- Disable selected entries: `--disable-dynsmf=<ids>` or
  `SIMPLE_DYNSMF_DISABLE=<ids>`

The startup adapter is a general dynSMF path. It records background compile
requests for enabled manifest entries whose artifacts are not ready, using the
same deterministic build plan as the wrapper:
`bin/simple compile <source> -o build/dynsmf/<id>.smf`. It then uses checked
autoload: enabled manifest entries must point to generated `.smf` artifacts with
`SMF\0` magic before `smf_dlopen_checked` returns a handle. Background compile
evidence never masks load failures; missing, short, or invalid artifacts still
record deterministic failed evidence rows until the wrapper or another compiler
worker materializes them. Plain app-root startup remains quiet; use
`--dynsmf-status` when operator or test evidence is needed.

Each successful background compile writes three sidecars next to the artifact:
`<id>.smf.srchash` (whole-source hash), `<id>.smf.ifacehash` (heuristic hash of
exported-signature lines only), and `<id>.smf.abi` (the manifest `abi_version`).
Artifact status is fail-closed on all three: a missing or mismatched `.abi`
sidecar reports `abi_mismatch` and the artifact is never loaded; a srchash
mismatch is split by the interface hash into `stale_impl` (exported interface
unchanged — recompiling the module alone is sufficient) versus
`stale_interface` (exported interface changed — dependents need a rebuild too);
a legacy artifact without an `.ifacehash` sidecar falls back to the generic
`stale_source`. Before any sidecar is consulted, artifact status also runs an
export-witness check (`smf_artifact_has_export` in `smf_dynlib.spl`): it scans
the artifact's own bytes for each name in the manifest entry's `exports` list
as a null-terminated ASCII run — the same convention the real SMF string
table uses — and unconditionally requires the payload to exceed the known
219-byte hollow-stub size, since a bare name match alone is not sufficient
(the stub already contains a literal `main` symbol). A hollow artifact (e.g.
the stub described in
`doc/08_tracking/bug/seed_compile_smf_stub_fail_open_2026-07-17.md`) reports
`stub_artifact` and is never loaded regardless of how fresh its sidecars are.
`--dynsmf-status` prints one `id:reason:ready=` line per entry.

## Current Limitations

- **Libraries must be pre-registered**: `dylib_async_open` calls
  `dylib_registry_open(path)`, which only finds libraries previously registered
  via `dylib_registry_register(path, bytes)`. Unregistered paths return ENOENT.
- **SMF registry symbols are not executable mapping evidence**: the registry can
  resolve ELF/SMF symbol values from registered bytes, but that does not prove
  the address is mapped into the host process with executable permissions. Hot
  perf probes must report this as `call_source=registry_symbol_only` and fail
  closed until true SMF executable mapping exists. Use
  `dynlib_symbol_is_process_callable` before dispatching through
  `dynlib_call_0..6`.
- **Runtime dyncall bridge exists**: `rt_dyncall_0..6` are implemented in the
  Rust runtime for `i64` arguments and `i64` return values. They are valid only
  for process-callable function pointers.
- **Host shared libraries use a separate WFFI path**:
  `src/lib/nogc_sync_mut/sffi/dynamic.spl` wraps `spl_dlopen`, `spl_dlsym`, and
  `spl_wffi_call_i64` for `.so`/`.dylib` host libraries. That proves host dynlib
  calls, not SMF dynlib acceptance.
- **Legacy runtime SMF file helpers are not the GUI release lane**:
  `rt_file_wrap_smf_dynlib` and `rt_file_extract_smf_dynlib` still exist as
  generic runtime helpers, but they are not accepted GUI release-lane evidence.
  The pure GUI SMF path wraps and validates the role-2 artifact in Simple via
  `src/app/gui_perf/smf_dynlib_artifact.spl`, resolves loader parity through
  `src/app/gui_perf/simpleos_smf_dynload.spl`, and measures hot response with
  `src/app/gui_perf/smf_dynlib_probe.spl`. Acceptance still requires
  `loader=smf_dynlib`, `call_source=dynlib_symbol_call`, no fallback, the full
  expected sample count, and p99 below the configured threshold.

## Testing

```bash
bin/simple test test/01_unit/os/posix/dynlib_spec.spl
bin/simple test test/01_unit/os/posix/dylib_async_spec.spl
bin/simple test test/01_unit/os/smf/smf_dynlib_spec.spl
bin/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl
```
