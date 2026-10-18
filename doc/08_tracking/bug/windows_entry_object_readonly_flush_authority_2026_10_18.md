# Windows entry-object publication lacks read-only flush authority

Status: OPEN. The native Windows file provider below is a qualified subset;
`--emit-entry-object` remains blocked. This is not a successful entry-object
publication fix and does not admit a compiler, runtime, or bootstrap phase.

## Reproduction and cause

The actual Windows producer `0405`, source snapshot `b790`, compiled the Hello
entry to a genuine 631-byte AMD64 COFF object and its original capsule receipt.
Its public copy failed with `entry-object-source-root-unavailable` because
`rt_cache_host_open_root_v1` was unsupported in the native C provider.

Implementing open/read/temp/publication exposes the next required barrier:
`driver_native_entry_object_receipt_barrier_v1` flushes the original receipt,
original object, and source directory. The published object and destination
directory are also flushed. Both original and published object capabilities
are read authorities, and a fresh published object is read-only.

Windows `FlushFileBuffers` requires a write-capable file handle. A direct native
probe on this host returns `ERROR_ACCESS_DENIED` for read-only handles, and
`NtFlushBuffersFile` returns `STATUS_ACCESS_DENIED` for the same handles. Both
succeed on a directory handle opened with `GENERIC_READ | GENERIC_WRITE`.
`ReOpenFile` does not support directory handles; a checked open of the locked
directory's final path is required to obtain its writable flush handle.

Primary contracts:

- [FlushFileBuffers](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-flushfilebuffers)
- [NtFlushBuffersFileEx](https://learn.microsoft.com/en-us/windows-hardware/drivers/ddi/ntifs/nf-ntifs-ntflushbuffersfileex)

## Qualified native C subset

`src/runtime/runtime_cache_host_authority_v1.c` implements root, regular-file
read, bounded whole-file receipt read, secure temp, bounded write, atomic
no-replace publication, flush, and close. It retains every directory ancestor
without delete sharing, checks reparse attributes and final handle paths,
excludes write/delete sharing on immutable read handles, and uses opaque random
capability tokens. Temp publication flushes the real file before and after
handle-based rename, marks it read-only, and consumes the temp capability.
Collision preserves the destination and seals the temp until cleanup.
Publication alone does not claim directory durability: callers must separately
check root sync. The production entry-object caller still fails at read sync.

Root sync performs a real `FlushFileBuffers` on a writable handle when granted;
permission denial remains failure. Read sync explicitly remains unsupported.
CAS traversal, daemon, reader-pin, namespace, and GC admission remain unsupported.
UNC/device roots and reparse traversal fail closed. No path-only escape or
synthetic durability success was added. The original receipt is never rewritten.

## Evidence

LLVM-mingw `gcc`, native Windows, 2026-10-18:

```text
gcc -std=c11 -Wall -Wextra -Wno-unused-parameter \
  src/runtime/test/rt_cache_host_windows_v1_selfcheck.c \
  src/runtime/runtime_cache_host_authority_v1.c -o authority.exe
PASS Windows cache file authority: 113 checks
```

SHA-256 of the retained native executable:
`7971224633b02411bf49489eeeaef9c3bb5b5a49faa44a7413a8dc71dc041927`.
SHA-256 of its test source:
`83df6e4ac775973c7894559a8f826dd14c598622f31c29aadb12dfb31205c881`.
The final provider diff after that run changes one explanatory comment only.
Retained stdout, executable, tested source snapshot, compiler identity, and
SHA-256 receipt: `build/native_probe/windows-cache-authority-20261018/receipt.json`
in worktree `C:/dev/simple-cache-authority` (local evidence, not committed).
The production C translation unit also compiled with LLVM `clang-cl /c /MT
/std:c11` against the discovered MSVC/Windows SDK includes. Its AMD64 COFF object
SHA-256 is `92408f25e873d8f44e8867f7f32200a65c8f7e985a8e40984fb9dd31ab268400`.
This compile check does not admit the whole runtime or exercise an MSVC-linked
selfcheck. The existing environment setup reported its optional pinned LLVM
path missing; the explicit `C:/Program Files/LLVM/bin/clang-cl.exe` compile
succeeded after SDK include discovery.

The executable verifies Unicode paths longer than 260 characters, mandatory
junction rejection, malformed/escaping paths, root and nested-directory rename
denial, immutable receipt bytes and writer denial, bounded/empty reads, actual
directory flush, temp flush, read-only publication, no replacement, sealed
collision cleanup, stale handles, and descendants surviving root close. It
also asserts original and published read-only flush return failure, so this
remaining production barrier cannot be mistaken for a passing integration.

Three focused verification cycles were used: initial 110 checks passed;
adding production flush coverage exposed directory `ReOpenFile` failure;
locked final-path directory acquisition passed 113 checks. No full CLI,
compiler test suite, or successful public entry-object copy was claimed.

## Required completion

Design an explicit flush authority that can retain the original writer's
flush-capable handle through immutable receipt admission and publication,
including already-published read-only destinations and capability lifetime.
Do not temporarily make original receipts writable or treat a failed flush as
success. Verify the complete production barrier/copy sequence through its ABI
before claiming `--emit-entry-object` works. Normal native-build routing may
continue independent bootstrap diagnostics; it does not satisfy this criterion.
