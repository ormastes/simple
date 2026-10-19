# FILE-WRITE-SPAN-ABI

Status: source repair with authored regressions; execution UNRUN.

The safe io_file_write_all facade previously declared rt_io_file_write_all(fd, [u8]), but the selected hosted provider requires fd, byte pointer, byte length. An array handle is not a byte address. Port the previously reviewed owner adaptation; retain safe facade return types and descriptor borrowing. Add the matching single-write facade for the existing provider without turning partial writes into write-all.

Packed data is retained across the synchronous foreign call. Generic word arrays copy into checked packed storage, validating each byte and checking final extent. No data pointer escapes, no descriptor is closed, no global cache is introduced. Empty write-all keeps the provider's no-syscall behavior; single-write calls its provider once (provider owns EINTR handling). Negative/greater-than-INT_MAX descriptors fail before foreign calls. No IoError constructor or session API changes.

Evidence: runtime_native.c declares rt_io_file_write(int64_t,const uint8_t*,uint64_t) and matching bool write_all. Source implementation remains Simple; C is read-only ABI evidence. Pointer/length transport here is the existing 64-bit native route; 32-bit support is not qualified. No new runtime symbol is invented. No corresponding file writer was found in the bounded simple_core inventory.

Four API scenarios and the standalone native fixture check generic/packed byte equality including NUL/128/255, empty write-all, invalid descriptors, and real read-only descriptor errors with caller-owned close. Deterministic short-write injection, allocation failure, actual selected provider identity and generated [u8] tagging remain unqualified. No source-predicted result is an executed PASS.

Root baseline SFFI audit failed before backlog generation (source_variants405/399; migration3619/3546). Preserve that preexisting debt; no baseline rewrite, exemption or blanket migration. No compiler/test/build ran for this port.
