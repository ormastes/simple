# Loader executable memory

Source: `test/02_integration/app/loader_exec_memory_spec.spl`

Requirement: `REQ-SSPEC-INTEGRATION`.

This manual describes the production loader mapping and function-call checks.
Execution against an admitted Phase 2 compiler and test runner is pending.
This is an authored manual; regeneration by the admitted `spipe-docgen` remains
part of verification.

| Scenario | Hosts | Required observations |
|---|---|---|
| copies real bytes into a loader-owned mapping | All supported hosts | Positive address, four bytes written at offset 64, exact readback, successful release |
| rejects invalid sizes and function addresses deterministically | All supported hosts | Zero and negative sizes rejected, null call returns the expected error, null release rejected |
| seals and executes an x86_64 function through the production loader | x86_64 only | Writable allocation, six bytes written, successful executable transition, `Ok(42)`, successful release |

## Copy bytes into a real mapping

1. Allocate 4096 bytes through `native_alloc_exec_memory`.
2. Write `[17, 34, 51, 68]` at offset 64 through `native_write_exec_memory`.
3. Read four bytes from the same offset through `native_mmap_read_bytes`.
4. Release the mapping and check the exact write count, readback, and release
   result.

## Reject invalid requests

1. Request allocations of zero and negative size; both must return zero.
2. Call address zero through `native_call_function_0`; it must return the
   documented error without invoking an entry point.
3. Release address zero; the loader must reject it.

The allocation checks use deterministic invalid inputs. Large positive virtual
allocations may legitimately succeed on operating systems with overcommit.

## Execute an x86_64 function

1. Allocate a writable mapping and copy `mov eax, 42; ret` into it.
2. Change the mapping to executable through `native_make_executable`.
3. Call the mapped entry point through the production Result-returning API.
4. Release the mapping, then require `Ok(42)` and successful release.

This no-argument code works with the x86_64 Windows and POSIX calling
conventions. Other architectures register only the two architecture-independent
scenarios; they do not claim machine-code execution coverage.

## Evidence

Run this spec separately in interpreter and compile modes through the admitted
Phase 2 command owners. Require three executed scenarios on x86_64 and retain
both terminal JSON results. A source review or an unadmitted release executable
does not satisfy this gate.

See `doc/09_report/loader_binary_phase2_verification_2026-09-21.md` for the exact
admission blocker, existing test coverage, and resume commands.
