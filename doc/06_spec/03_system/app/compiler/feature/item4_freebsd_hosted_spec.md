# FreeBSD hosted input and ELF identity contract

Authority: `test/03_system/app/compiler/feature/item4_freebsd_hosted_spec.spl`.
Requirements: ITEM4-REQ-005, 006. Status: authored manual; execution and canonical
regeneration are **UNRUN**.

1. Link actual code plus an unreferenced allocated FreeBSD ABI note. Verify its
   complete identity, version payload and corresponding PT_NOTE range.
2. Brand a real linked image as FreeBSD. Independently zero the build-id digest,
   hash the image, and compare the resulting digest. Require idempotent resealing.
3. Corrupt ELF identity input and require rejection.
4. Construct a task-owned sysroot for path selection. Assert complete executable
   and PIE CRT order, target interpreter and optional split-library precedence.
5. Delete a required startup object and require its named diagnostic.

Sysroot fixture contents test selection only; they are not admitted FreeBSD CRT
or loader binaries. Native execution belongs to the separate platform scenario.
