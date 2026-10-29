# Authenticated loader sealed source acquisition

Executable: `test/01_unit/os/kernel/loader/executable_sealed_source_v1_spec.spl`.
Requirement: REQ-SOSIX-MEMORY-SOURCE-002. Manual scenario record; hosted
interpreter diagnostic evidence, 3 executed / 3 passed / 0 skipped / 0 dropped.

The three scenarios execute the same lifecycle through real MountTable DBFS,
NVFS and NVFS POSIX facade instances. NVFS in this test uses its hosted DBFS
backing; it is not hardware or QEMU NVFS evidence.

1. Write `[0, 255, 128, 65]` to a retained filesystem handle.
2. Supply a diagnostic pathname different from the actual source name; acquire
   by the retained handle and check exact bytes and unchanged retained charge.
3. Modify the source file. The acquired snapshot stays unchanged; a new
   acquisition against the prior digest returns `DigestMismatch`.
4. Request a length beyond EOF and require `SourceReadFailed`.
5. Close the retained handle, reject acquisition, and verify no leaked charge.

These source handles are diagnostic metadata. Executable authority remains
with the separate signed admission/token/scheduler path; this suite does not
issue or forge that authority.
