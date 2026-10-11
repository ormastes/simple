# Target 6 native CAS byte-write repair (2026-10-11)

## Cause

The admitted Stage2 LLVM build lowered `rt_file_write_bytes(path: text, data: [u8])` to an incompatible raw call: the eight-byte ELF probe wrote 255 bytes of array metadata. Two array-to-text/array-aware variants also failed. Disassembly of the raw-pointer probe showed that a `text` argument to the new extern is passed through `rt_interp_cstr` as a C string. Its first C implementation expected a tagged Simple text value, so it rejected the path before opening the staged file.

## Repair

`sosix_file_write_new_bytes_v1` now copies typed bytes into a bounded 1 MiB raw host buffer, calls a C-string-path positional writer, checks the exact byte count, and releases the buffer. The C writer exclusively creates the first chunk and uses `O_NOFOLLOW` where available. CAS object and action receipt staging call the SOSIX facade. CAS retains its digest readback before publication.

## Evidence

The no-stub admitted Stage2 LLVM entry-closure build succeeded with 36 native modules. The executable fixture passed valid archive admission, semantic-only rejection, target mismatch, duplicate symbol rejection, NUL/high-byte CAS round trip, and a 1,048,583-byte CAS object crossing the chunk boundary. The fresh extended run printed `PASS archived native object CAS admission`; `/usr/bin/time` reported 0.56 s and 13,596 KiB peak RSS. Build log: `/tmp/simple-target6-cas-chunk-fixture-build-20261012.log`. Earlier ABI traces are named in the linked [defect record](../../08_tracking/bug/target6_archive_native_fixture_cas_publication_2026-10-11.md).

The admitted Stage2 executable is a limited native-build runtime: an attempted `run --mode=interpreter` returned `unknown command run`. The SPipe regression is updated but cannot be executed there. Full core/MCP smoke, production native cohorts, and Item 6 qualification remain open.
The subsequent alias-only routing of CAS read, publish, temporary-directory, and cleanup calls through SOSIX passed its own no-stub Stage2 LLVM rebuild and fresh-root executable fixture. That run printed `PASS archived native object CAS admission`; `/usr/bin/time` reported 0.57 s and 13,916 KiB peak RSS. Build log: `/tmp/simple-target6-cas-sosix-alias-build-20261012.log`.
