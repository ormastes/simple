<!-- codex-design -->
# RV32 privilege-transition ABI

## Decision

RV32 live execution remains fail-closed until one architecture owner implements
this v1 contract. The owner receives an admitted ELF, the explicit Sv32 root,
and a kernel-owned execution token; it alone may install the root, publish the
supervisor continuation, enter U-mode, dispatch the resulting ecalls, and reap
the address space.

The deployable v1 target profile is RV32IMAC plus privileged Zicsr support with
the ILP32 calling ABI. Its fixed 160-byte, 16-byte-aligned frame reserves
x1-x31, trap CSRs, supervisor-stack top, interrupted SATP, and three zero words.
Admission requires `sstatus.FS=Off`; trap and return code execute no F/D
instruction and reject a frame whose saved FS bits are nonzero.

RV32IMAFD/ILP32D is a distinct future v2 capability profile with a 416-byte
frame and a full D-width register bank. V1 and v2 may not share entry/vector
symbols or be selected implicitly. V2 remains unavailable until a target owner
proves F/D and links a matching privileged object.

## Privilege boundary

`stvec` uses direct mode and a four-byte-aligned `_rv32_trap_vector`.
Immediately before U execution, `sscratch` contains a 16-byte-aligned pointer
to the privileged per-hart trap anchor. The anchor contains supervisor-stack
top, token pointer, hart ID, and nesting state. A U trap swaps user `t0` with
`sscratch`, validates the anchor, switches to its stack, saves the displaced
user `t0`, and clears `sscratch`. While S-mode code runs, `sscratch` is zero, so
a nested supervisor trap stays on the current supervisor stack and is never
authenticated as a user trap. First entry clears SPP, sets SPIE, sets `sepc`,
installs authenticated SATP, executes `sfence.vma`, publishes `sscratch`, then
restores the frame and executes `sret`.

The token binds `(task_id, task_generation, address_space_generation,
root_phys, expected_satp, asid, nonce_token, hart_id)`. All identities are kernel-issued,
nonzero, and immutable after Prepared. The ASID is the nine-bit Sv32 ASID; root
PPN occupies SATP bits 21:0. Every U trap checks the token and observed SATP.
No value copied from user memory can reconstruct or extend this authority. A
nonzero SipHash-2-4 tag covers every immutable binding field, including hart
ID. ABI v1.2 uses a 128-bit per-boot key owned only by the transition registry.
The fixed C boundary accepts a 16-byte key pointer, message pointer, and u32
length and returns the 64-bit result through the ILP32 `a0/a1` pair. Standard
key bytes `00..0f` and an empty message produce `0x726fdb47dd0e0e31`.

Publishing an anchor is a release operation after the complete token,
continuation, frame, and stack are initialized. Trap lookup acquires it before
reading any field. Publication rejects nonzero token pointers or non-idle
nesting; it never replaces an occupied slot. Return to U transitions nesting
1 to 0 before release-republishing the anchor in `sscratch`. Exit consumes the
continuation, clears token pointer and anchor with release ordering, then makes
the slot reusable. A nested S trap sees `sscratch=0`, uses the current stack,
and follows the supervisor fault/interrupt path without changing nesting.

The MAC input is exactly 80 bytes. Bytes 0..15 are ASCII
`SOSIX-RV32-TOK1` followed by NUL; bytes 16..19 are ABI version; task ID, task
generation, address-space generation, root physical address, and nonce token
are u64 at offsets 20, 28, 36, 44, and 52; expected SATP is u32 at 60; ASID is
u16 at 64; bytes 66..67 are zero; stack bottom, stack top, and hart ID are u32
at 68, 72, and 76. All integers are unsigned little-endian. Mutable lifecycle
state and the tag itself are excluded.

The registry obtains exactly 16 bytes from the admitted boot entropy owner
before publication. Missing, short, or all-zero key material leaves it
unavailable and entry fails closed. The key is never returned, logged, mapped,
or copied into a token. Reset/shutdown release-clears anchors, wipes the key
with volatile byte stores, verifies zero storage, then marks it unavailable.
Verification recomputes the tag and compares all eight bytes using accumulated
XOR with no tag-dependent branch. An Entered token cannot migrate. Migration
after reap requires a new generation, nonce token, and tag.

## Call and lifecycle contract

The assembly dispatcher ABI is
`rv32_dispatch_user_trap_scalar_v12(request*) -> i32`. The request points to
the kernel trap frame and token and records observed SATP and privilege. The
per-hart owner validates and commits all token/scheduler state before returning
one encoded disposition in `a0`: 0 ReturnToUser, 1 ResumeSupervisor, or -1
Reject. No enum or aggregate crosses the assembly boundary. Only U-mode ecall
cause 8 is accepted. `a7=60` consumes the byte in
`a0` under the admitted nonce transcript contract. `a7=0, a0=37` is the only
successful exit. The dispatcher advances `sepc` by four only for an accepted
ecall.

Lifecycle is strictly `Prepared -> Entered -> Exited -> Reaped`. Exit consumes
the saved S continuation once, switches to kernel SATP, fences, marks the exact
child exited with 37, and resumes the saved kernel SP. Reap by the parent owns
the sole destruction of the explicit Sv32 root, frame, and supervisor stack.
Stale generation, wrong SATP/root/ASID/nonce, S-mode ecall, replayed exit, or a
second reap is fatal and cannot resume U-mode.

## Ownership

The v1 constants and C-layout structures in
`src/os/kernel/arch/riscv32/privilege_transition_abi.spl` are the single ABI
source. The v2 constants reserve a future profile, not an implementation.
Assembly and dispatcher code do not yet exist. The existing simulator
is evidence about payload bytes only, never evidence of this transition.
