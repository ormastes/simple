# Windows SMF file-backed raw mapping

Status: FIXED (2026-09-21)

## Failure

Windows could not load an SMF through the production file-mapping API. Both C
providers rejected every `rt_mmap_raw` call whose descriptor was not `-1`, and
the Rust interpreter reported `rt_open_fd is unavailable on this host`.
Windows unmapping also always used `VirtualFree`, which cannot release a view
created by `MapViewOfFile`.

The executable regression spec
`test/01_unit/compiler/loader/windows_file_mmap_spec.spl` was red before the
fix through `compiler.loader.smf_mmap_native.native_mmap_file`: the two mapping
examples both failed. It uses the real loader API and checks byte-accurate
mapping, private copy-on-write behavior, and safe rejection of a closed
descriptor.

## Fix

- The native Windows providers share `windows_raw_mapping.h`, which maps CRT
  descriptors with `CreateFileMappingA` and `MapViewOfFileEx`.
- `MAP_PRIVATE` writable views use `PAGE_WRITECOPY` and `FILE_MAP_COPY`.
- Unmapping distinguishes mapped views from `VirtualAlloc` reservations.
- Invalid CRT descriptors are contained with a thread-local UCRT invalid
  parameter handler and return `-1` without terminating the process.
- The Rust interpreter owns opaque Windows file tokens and implements the same
  file mapping, copy-on-write, and release behavior.

## Evidence

- Fresh Rust driver build: PASS.
- Executable regression spec after the fix: 3 examples, 0 failures; verdict OK.
- Native `runtime.c` clang-cl probe: read mapping/unmap PASS and writable
  private copy-on-write plus closed-descriptor rejection PASS.
- `runtime_native.c` standalone and `runtime_legacy_core.c` compile with
  clang-cl: PASS.
- `scripts/audit/mmap-provider-contracts.shs`: PASS.

Native evidence used only:

- `C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe`
- version `23.1.1`, LLVM revision
  `6dfe1677ab8dffbc6ec13d53a1e0215d75147689`
- SHA-256
  `D43B7FA07B5B77B716E60600AD2792CFB2EEB370AECB6144BF6C698F2C6D7467`

This issue is independent of PR #1201, which covers executable-memory evidence.
