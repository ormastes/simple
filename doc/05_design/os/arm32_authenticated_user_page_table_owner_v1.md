# ARM32 authenticated user page-table owner v1

## Scope

This owner turns the already authenticated ARM32 PT_LOAD plan into a private
short-descriptor L1/L2 tree. It deliberately does not consume loader authority,
publish a task, switch TTBR0, or transfer control to user mode.

## Ownership

`user_page_table_owner_v1.spl` is a serialized, four-slot capsule. A slot owns
one explicit 16 KiB L1 root, every allocated 4 KiB L2 backing frame with its
exact L1 index, every mapped PT_LOAD frame, and the mapped pages containing the
initial ELF32 stack frame. Public/package receipts contain generation and nonce
coordinates, not a transferable destructor or execution capability.

The ARM32 paging leaf provides only exact-root primitives. Root creation copies
the kernel half from the active ARM32 root. Mapping rejects zero, unaligned,
kernel-half, replacement, and over-32-bit addresses. W+X requests are lowered
to writable/non-executable mappings. Exact unmap compares the expected frame
before clearing a leaf.

## Mapping algorithm

The owner revalidates armed identity, authenticated handle, source digest,
ELF32/EM_ARM layout, launch arguments, and load-plan consumer before allocation.
It advances the canonical consumer through `Validated`, `Mapping`, and
`MappedBlocked`, requiring its mapped count to equal the authenticated plan.
Each admitted
segment is mapped page-by-page. A page is zeroed once, then its file-backed
intersection is copied directly and read back. BSS therefore remains zero
without a second 4 KiB staging allocation. The shared stack builder serializes
four-byte argc/argv/envp/auxv words; only pages intersecting that frame are
allocated, zeroed, copied, and read back. Work is O(source-backed bytes plus
mapped pages); retained metadata is bounded by 65,536 pages, 2,048 L2 tables,
and four live slots.

## Failure and teardown

Rollback visits leaves in reverse order and exact-unmaps before freeing frames.
The root destructor requires a one-to-one match between every user L1 page-table
descriptor and the owner's bounded `{l1_index, phys}` records, refuses aliases,
nonempty tables, or replacements, clears user L1 pointers, frees each authenticated
L2 frame once, then frees the aligned four-page L1 allocation. A
partial rollback publishes the residual identities as `Quarantined`, allowing
the same generation-bound receipt to retry destruction without double-freeing
already released pages.

Before a future scheduler consumes the loader token, the mapping owner can
atomically transition one exact generation/nonce receipt from `MappedBlocked`
to `AdoptionReserved`. A repeated or stale reservation is rejected. If later
scheduler preparation fails, the same owner can roll the receipt back to
`MappedBlocked`; neither transition grants execution. Final destruction
releases stack and PT_LOAD pages, advances the bound load consumer through
unmap/close, and requires `Released`.

## Remaining non-readiness

The global ARM32 execution dispatch remains false. Completion still requires
the scheduler to consume an `AdoptionReserved` mapping as an owned move, publish
the TCB and vmspace atomically, switch TTBR0 with the required barriers, and
perform real SVC/user entry and reap, followed by filesystem-backed QEMU
evidence. This mapping receipt always reports
`execution_authorized=false`.
