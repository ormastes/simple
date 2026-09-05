<!-- codex-design -->
# ARM32 privilege-transition ABI detail design

## Frozen records and ports

`Arm32SvcFrameV1` is an assembly-written 18-word record. The vector saves
r0-r12 first, obtains User SP/LR with the ARM privileged banked-register form,
normalizes SVC LR to the faulting instruction address, copies SPSR, and records
the fetched instruction. C/Simple consumers may not extend this record.

`Arm32UserHandoffTokenV1` is a scheduler-written 16-word record. Token memory
is kernel-only, pinned, 8-byte aligned, and remains live until REAPED. The auth
tag is SipHash-2-4 over exactly 72 bytes: domain `SOSIX-A32-TOK1.1`, then
little-endian words 0..11 and 14..15. It covers identity, continuation, state,
`expected_frame_sp`, and `syscall_sequence`, while excluding its own words
12..13. The 128-bit key is boot-private and absent from the token. Verification
uses XOR/OR over both stored tag words without a mismatch-dependent early exit.

The platform fixes `arm32_vector_table_v12` in `.vectors.arm32.v12` and
retains it before entry text. CPU identity is MPIDR.Aff0 with four maximum
slots. Entropy bootstrap accepts exactly 16 nonzero bytes once, copies them to
scheduler-private storage, and volatile-wipes the caller buffer on success or
failure.

The frozen C ports are:

- `arm32_vector_install_v1(vector_phys)`
- `arm32_user_l1_create_v1(root_out)`
- `arm32_user_l1_map_v1(root, va, pa, flags)`
- `arm32_user_l1_destroy_v1(root, address_space_id)`
- `arm32_enter_user_v1(token, entry, user_sp)`
- `arm32_svc_dispatch_v1(frame, token, observed_ttbr0)`
- `arm32_token_registry_bootstrap_v11(cpu_count, boot_secret)`
- `arm32_token_issue_v11(...)`
- `arm32_token_lookup_active_v11(cpu_id)`
- `arm32_token_authenticate_v11(cpu_id, frame, observed_ttbr0)`
- `arm32_token_advance_v11(cpu_id, expected_state, next_state)`
- `arm32_token_revoke_v11(cpu_id, task_id, task_generation)`

The dispatcher returns only REJECT, RETURN_USER, or RESUME_SUPERVISOR. Assembly
selects its epilogue from that closed enum and performs no scheduler policy.

Mapping is page-only. A private 16-KiB L1 owns dedicated zeroed 4-KiB pages for
coarse L2 tables and never emits sections. User RX is AP=110/XN=0; user RW is
AP=011/XN=1; user RO is AP=110/XN=1; normal memory is WBWA. Shared device RW is
AP=011/XN=1/TEX:C:B=000:0:1/S=1. Every user page is nG/domain0-client.
Unknown flags, missing USER, W+X, device EXEC, and unshared device mappings fail
before mutation.

## Entry sequence

1. Scheduler reserves TaskId/generation and a fresh address-space ID.
2. MMU owner creates an aligned private L1 and maps validated PT_LOAD/stack
   pages through the explicit root.
3. Scheduler allocates a 4-KiB SVC stack with an unmapped guard page below it.
   Its top is 8-byte aligned and `expected_frame_sp = top - 72`. It issues the
   token into the privileged per-CPU registry, computes its authentication tag,
   commits PREPARED, and records the expected frame.
4. Entry assembly masks interrupts, validates token shape and tag through the
   dispatcher, saves the supervisor continuation, switches TTBR0 with barriers,
   installs User SP/LR and SPSR=`0x10`, transitions RUNNING, and exception
   returns to the aligned entry PC.
5. SVC entry captures the fixed frame and dispatches only syscall 60 or 0.
6. Exit 37 restores kernel TTBR0 and supervisor SP/PC, marks EXITED, resumes
   scheduler code, and reaps the same TaskId/generation before destruction.

## Static acceptance and sabotage

The C contract uses `_Static_assert` for all cross-language sizes and critical
offsets. The focused C sabotage fixture requires a valid token to pass shape
checks and rejects a missing authentication tag, wrong observed TTBR0, and
misaligned supervisor stack. It proves auth words are excluded from MAC input
while generation, nonce, frame, and sequence mutations alter it.
Implementation tests must additionally sabotage
stale generation, wrong nonce/tag, privileged-origin SVC, frame relocation,
syscall replay, invalid output byte/range, wrong exit code, second exit,
premature L1 destruction, and reap of a different generation.
Mapping sabotage additionally covers unknown flags, W+X, executable/unshared
device pages, cache-policy drift, section descriptors, foreign-root L2
teardown, MPIDR slot 4, misaligned VBAR, zero entropy, and entropy non-wipe.

This design intentionally contains no vector assembly, context switch, page
table mutation, or scheduler integration. Those changes remain blocked until
each future owner consumes these exact v1.3 records and ports.

## v1.3 concrete storage and commit ownership

The table arena is a bounded parent-owned resource, not a general allocator;
its ledger is never user mapped. Allocation returns physical-address handles,
and the frozen identity-map rule lets SVC code access the same numeric address.
The child receives mappings and immutable nonce bytes only.

The active token is a borrowed kernel-only lease. SVC assembly may lookup and
authenticate it but cannot commit lifecycle changes. It returns one closed
encoded disposition to the scheduler, the sole owner allowed to commit
sequence/state, stdout, exit, reap, revoke, or table teardown. Transport is
bounded to one token and one 72-byte frame per CPU; nested SVC is rejected.

The C SipHash owner is fixed-buffer and allocation-free. Its canonical KAT
runs before bootstrap; failure leaves the registry uninitialized while still
wiping the supplied secret.

The v1.4 decoder returns `Arm32SvcDispositionV14` in caller-owned output
storage. Parent commit requires the exact current task, generation, sequence,
receipt, TTBR0, frame SP, and User SPSR plus zero reserved fields. Sabotage
mutates generation and receipt independently and replays a committed stdout
result; all are rejected before mutation.
The focused assembly consumer installs VBAR, creates the exact 72-byte frame,
uses a separate 64-byte disposition scratch area, dispatches and parent-commits,
then either exception-returns to User or restores kernel TTBR0 and the saved
supervisor continuation. Reject paths halt closed. Parent stdout capture is
bounded to 256 bytes; reap performs state advance, table teardown, and revoke
in that order.

## v1.5 concrete frame and guard design

The frame arena and its ledger are disjoint from page-table storage. ELF
staging validates header/program-table bounds, `filesz <= memsz`, ARM machine,
address overflow, alignment, and rejects writable-executable loads before it
allocates, zeros, copies, and maps frames. Failure tears down only frames owned
by that staged image.

Kernel SVC guard installation is owned by a four-slot lease table. It accepts
only an aligned root, aligned guard VA, and an existing section descriptor;
the owner expands the section attributes into all 256 small-page descriptors,
invalidates exactly the guard entry, and publishes the coarse descriptor with
architectural barriers. Teardown requires an exact root/guard/table match and
restores the saved section before freeing the L2 page.
