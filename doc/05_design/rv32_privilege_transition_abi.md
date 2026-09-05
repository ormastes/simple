<!-- codex-design -->
# RV32 privilege-transition ABI detail design

## Frame layout

The RV32IMAC v1 frame is 160 bytes aligned to 16 bytes. Offsets are: x1 at 0,
x31 at 120, `sepc` 124, `sstatus` 128, `scause` 132, `stval` 136,
supervisor-stack top 140, interrupted SATP 144, and three reserved-zero words
at 148 through 156. The reserved words must be zero on creation.
The GPR array uses architectural x-number order, so a register offset is
`(x - 1) * 4`.

V1 admits and restores only FS=Off. It contains no FP reservation and the trap
vector executes no F/D instruction. Nonzero saved FS bits reject the transition.
The separate RV32IMAFD/ILP32D v2 profile reserves the prior 416-byte layout with
FP offset 144 and `fcsr` offset 400, but is not selectable until hardware and
toolchain admission exist.

### Resolved profile decision

The repository's declared RV32 platform advertises
`riscv,isa = "rv32imac"` in
`examples/09_embedded/simple_os/arch/riscv32/soc_virt.dts`, and its documented
shim compiler profile is `-march=rv32imac_zicsr -mabi=ilp32`. There is no
RV32 target-admission owner that proves F and D or selects ILP32D. V1 therefore
matches RV32IMAC/Zicsr and ILP32 and requires FS=Off. The incompatible IMAFD
layout is versioned as v2 and remains future-only; runtime FS state cannot
silently select it.

## Entry sequence and dispatcher

The future owner validates root alignment/range, composes exact Sv32 SATP from
the bound ASID/root, and compares it to the token. It stores a
`Rv32SupervisorContinuationV1`, transitions Prepared to Entered, writes SATP,
fences, writes supervisor-stack top to `sscratch`, and enters through the frame
with SPP clear and SPIE set.

The direct trap vector distinguishes a U-origin trap before swapping stacks.
It materializes the fixed frame and calls the typed dispatcher. The dispatcher
authenticates the complete token before inspecting syscall arguments. A debug
write accepts only the admitted one-byte sequence (`a0`); exit accepts exactly
37. Any other trap/result returns RejectAndTerminate. Returning to U restores
the same token and frame. ResumeSupervisor consumes the continuation atomically
and cannot be replayed.

### Per-hart trap anchor (ABI v1.1)

V1.1 freezes a 16-byte, 16-byte-aligned kernel-only anchor per hart: stack top
at offset 0, token pointer at 4, hart ID at 8, nesting at 12. While U-mode runs,
`sscratch` is the anchor pointer. The trap prologue uses
`csrrw t0, sscratch, t0`: `t0` receives the anchor and `sscratch` temporarily
holds user t0. After acquiring and validating the anchor, it switches to the
anchor stack and stores the displaced user t0 in the architectural t0 frame
slot. It then writes zero to `sscratch` for the duration of S-mode handling.

Publication initializes token, continuation, frame, and stack, calculates a
nonzero kernel-keyed authentication tag over the immutable token fields plus
hart ID, then release-publishes the token pointer and anchor. An occupied token
pointer or nesting other than Idle rejects publication. Trap lookup acquires
the anchor and requires matching anchor/token hart IDs, valid authentication
tag, expected SATP, and nesting transition Idle to UserTrap.

Return-to-user changes nesting UserTrap to Idle and release-republishes the
same anchor address in `sscratch`. Accepted exit consumes the continuation once,
release-clears token pointer and anchor, and never republishes `sscratch`.
Nested S-mode traps observe zero `sscratch`, remain on the current supervisor
stack, route only to the S-mode fault/interrupt owner, and do not mutate anchor
nesting. User state, SATP, and frame contents cannot select an anchor.

The dispatcher is parent-authoritative: it validates the child/user request,
commits the canonical per-hart token and scheduler mutation, then returns only
a scalar disposition. Assembly never interprets a Simple enum/struct return and
never commits lifecycle state. Values are 0 ReturnToUser, 1 ResumeSupervisor,
and -1 Reject.

### Authentication-tag contract (ABI v1.2)

V1.2 uses SipHash-2-4 and the repository reference KAT. Its fixed C ABI accepts
16 key bytes, a message pointer, and u32 length and returns the 64-bit tag under
ILP32. The architecture freezes the exact 80-byte little-endian serialization:
a 16-byte domain, ABI version, immutable identity/address/nonce fields, stack
bounds, and hart ID. Mutable lifecycle and the tag are excluded.

The transition registry is the sole key owner. It receives exactly 16 admitted
entropy bytes before publication; missing, short, or all-zero keys fail closed.
It never exports the key and wipes it with volatile stores after release-clearing
all anchors on reset/shutdown. Verification compares the eight recomputed and
stored bytes through accumulated XOR. Entered tokens are hart-pinned; migration
rejects. A later hart requires a new generation, nonce, and tag after reap. The
anchor remains the sole mutable owner, and user state never receives either
kernel pointer.

### Implementation blocker: RV32 cryptographic boot entropy

The generic `os.crypto.entropy.crypto_entropy_bytes(16)` boundary is suitable
only when its platform provider is ready. The current RV32 owner explicitly
states that no true random source exists on its QEMU/OpenSBI path and exposes
only `entropy_seed_u64()`, derived from timer, wall-clock, DTB address, hart ID,
and a constant. That mixer is not admissible key material for v1.2.

Before the registry can mint tokens, RV32 boot must expose a fail-closed
production entropy provider returning exactly 16 bytes before U-mode entry, or
the boot interface must inject 16 independently generated bytes through a
measured, kernel-only handoff. The transition registry must call that named
owner once and remain unavailable on failure. The early-boot mixer must never
be used as fallback. Until then only serialization/KAT/static contract work is
safe; installing assembly plus an always-unavailable registry would not prove
the requested live lifecycle.

### Implementation blocker: fixed SipHash symbol ownership

Entropy discovery is now source-wired, but the fixed
`rt_rv32_token_siphash24` C symbol has no implementation and no unique RV32
runtime owner. The platform catalog admits both
`examples/09_embedded/simple_os/arch/riscv32/boot/baremetal_stubs.c` and
`src/os/kernel/arch/riscv32/boot/baremetal_stubs.c`. The former is an independent
RV32 runtime; the latter includes the complete RV64 freestanding runtime and
then adds RV32 shims. Adding the symbol to one leaves the other lane unresolved;
adding strong definitions to both risks duplicate ownership when source closure
selects both.

Before the registry publishes an authenticated anchor, extract one shared
architecture-common freestanding SipHash-2-4 C owner (or freeze mutually
exclusive target source selection) and make both RV32 runtime surfaces consume
it. The static gate must prove exactly one strong definition and run the frozen
empty-message KAT. A weak fallback is prohibited for token authentication.

### Packed key/message storage (implemented, source/static verified)

The strong SipHash owner is now extracted and its KAT passes, but the Simple
registry has no proven packed-byte pointer for the frozen C ABI. In the RV32
freestanding runtime, `rt_array_data_ptr_u8` aliases `rt_array_data_ptr`, whose
`RtArray.data` is `spl_i64*`; each logical u8 occupies a tagged 64-bit element.
The SipHash ABI instead consumes contiguous raw bytes. Passing that pointer
would authenticate array representation rather than the 16-byte key and
80-byte canonical message.

The architecture-common fixed packed-storage owner now supplies explicit
16-byte key and 80-byte message records with stable aligned addresses,
generation leases, exact scalar-byte copies, stale-lease rejection, and
volatile wipe before reuse. It is selected exactly once by the RV32 target and
is never mapped to user or DMA. The RV32 registry serializes the frozen 80-byte
message into a synchronous loan, invokes the sole SipHash owner, and releases
the message record before returning. The long-lived key remains an opaque
kernel lease and is wiped on registry shutdown. Publication of a live trap
anchor still requires the scheduler/dispatcher lifecycle wiring and live QEMU
evidence; this storage result alone is not runtime admission.

## Scheduler integration

Task generation is a new nonzero lifecycle generation, distinct from TaskId
and capability generation. Address-space generation changes whenever a slot or
root is recycled. The scheduler publishes the token only after ELF admission,
mapping, stack/frame allocation, and parent/child registration all succeed.
Rollback destroys unpublished resources. After accepted exit, the child is a
zombie until the exact parent collects it. Reap performs the only root and
stack destruction and transitions Exited to Reaped.

## Static acceptance gates

`scripts/check/check-rv32-privilege-transition-abi.shs` checks canonical size,
alignment, offsets, required bindings, lifecycle order, and fail-closed status.
Its self-test copies the inputs, sabotages frame size and SATP binding text, and
requires both corruptions to fail. Later assembly admission must add object
disassembly/layout checks before live QEMU is permitted.
