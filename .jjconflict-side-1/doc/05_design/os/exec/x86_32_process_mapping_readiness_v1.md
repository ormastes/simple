# x86-32 process mapping readiness v1

## Outcome

`executable_x86_32_mapping_owner_v1.spl` is the architecture-local,
pre-consumption owner for i386 mapping evidence. It accepts a validated
`ExecutableImageHandleV1` and the bytes re-read from that retained handle,
requires the canonical `simpleos/x86/simpleos` target, rechecks the SHA-256
digest, then parses exact ELF32/EM_386 entry and PT_LOAD records from those
bytes. The parsed layout must equal the authenticated handle layout.

The owner performs bounded validation over at most 64 load ranges. It rejects
zero-page mappings, arithmetic overflow, mappings below the null guard, ranges
above the 3 GiB user ceiling, and an entry point outside executable material.
It never commits or retrieves a loader token, opens a file, allocates page
tables, maps memory, or publishes a task. Every receipt therefore records
`authority_consumed = false`.

## Honest dispatch status

`executable_x86_32_process_image_ready_v1()` remains false and the canonical
dispatch row remains unchanged. Two concrete owners are still absent from the
transaction:

1. `stack_builder.spl` serializes only eight-byte SysV words and explicitly
   rejects a four-byte ABI, so an ELF32/i386 initial stack cannot yet be built.
2. `user_address_space.spl` routes x86-32 through the generic PML4
   `vmm_address_space` implementation. The real x86-32 paging module can create
   a two-level page directory, but only maps through its global kernel root;
   it has no explicit-root map, rollback, or bounded root-destruction owner.

Flipping `process_image_builder_ready` before both gaps are closed would let
joint reservation consume authenticated authority before mapping can succeed.
The loader/scheduler must call this owner with bytes from the retained handle
while the token is still Armed, then use an
x86-32-specific address-space lease whose rollback frees all leaf frames and
private page tables before readiness becomes true.
