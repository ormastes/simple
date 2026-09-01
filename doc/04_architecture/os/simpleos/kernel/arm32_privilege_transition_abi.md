<!-- codex-design -->
# ARM32 privilege-transition ABI

## Decision

ARMv7-A user execution uses one architecture-owned transition capsule with
three ports: an exception/vector adapter, an explicit-root short-descriptor MMU
adapter, and the scheduler lifecycle owner. No generic x86 VMM function or
synthetic context helper may implement an ARM32 transition.

The frozen ABI is version 1.4 (`0x00010004`). Its source authorities are
`user_transition_contract.spl` and `arm32_user_transition_contract.h`.
Assembly is a consumer of those offsets, never their owner.

## Vector and exception ownership

The ARM32 boot architecture owns a 32-byte-aligned vector table in a linker
`KEEP` section and installs its physical address in VBAR before enabling user
execution. The SVC vector switches to a private, guard-bounded SVC stack, saves
`Arm32SvcFrameV1`, reads TTBR0, and calls `arm32_svc_dispatch_v1`. Undefined,
prefetch-abort, data-abort, IRQ, and FIQ entries cannot alias the SVC decoder.

`Arm32SvcFrameV1` is exactly 72 bytes: r0-r12 at 0..48, banked User SP at 52,
User LR at 56, normalized return PC (`SVC LR - 4`) at 60, SPSR at 64, and the
fetched SVC instruction at 68. SPSR mode must be `CPSR_USR`, the return PC must
be ARM-state aligned, and User SP must be AAPCS 8-byte aligned. Return to User
mode is by an exception-return instruction restoring SPSR; branching to the
entry while still in SVC mode is forbidden.

## Address-space ownership

The only admitted MMU interface is `arm32_user_l1_{create,map,destroy}_v1`.
Roots are nonzero 16-KiB-aligned physical L1 addresses. Mapping takes the root
explicitly and rejects the kernel root, stale address-space identity,
misalignment, kernel-range user mappings, and writable+executable pages. It may
copy the established upper-half kernel mappings, but it never mutates the
global boot root when a user root was requested. TTBR0 writes are followed by
DSB, TLB invalidation, DSB, and ISB.

The v1.2 flags are closed: USER=1, WRITE=2, EXEC=4, DEVICE=8, SHARED=16.
USER is mandatory; unknown bits, W+X, executable device memory, and unshared
device memory are rejected. Only 4-KiB small pages are emitted:

| Mapping | AP | XN | TEX:C:B | S | nG | Domain |
|---|---:|---:|---:|---:|---:|---:|
| normal user R-X | 110 | 0 | 001:1:1 (WBWA) | requested | 1 | 0 |
| normal user RW- | 011 | 1 | 001:1:1 (WBWA) | requested | 1 | 0 |
| normal user R-- | 110 | 1 | 001:1:1 (WBWA) | requested | 1 | 0 |
| shared device RW- | 011 | 1 | 000:0:1 | 1 | 1 | 0 |

Domain 0 is DACR Client, never Manager. Each coarse L2 consumes a dedicated,
zeroed 4-KiB physical page; only its first 1 KiB is used. The L1 owner records
every L2 page against its address-space ID. Destroy switches away from an
active root, invalidates its TLB, zeroes/frees recorded L2 pages, then frees the
16-KiB L1. Partial failure unwinds only pages recorded by that root. Section
descriptors are forbidden.

## Authentication and lifecycle

The scheduler creates exactly one 64-byte `Arm32UserHandoffTokenV1` per
committed child generation. It binds task ID, task generation, address-space
ID, user TTBR0 root, 64-bit execution nonce, supervisor SP/continuation PC,
kernel TTBR0, expected frame SP, syscall sequence, lifecycle state, and a
kernel-secret authentication tag. The canonical MAC is repository-owned
SipHash-2-4 (`src/os/crypto/siphash.spl`) with a scheduler-owned 128-bit boot
key. Its input is exactly the 16 ASCII bytes `SOSIX-A32-TOK1.1`, followed by
little-endian token words 0..11 and 14..15 (72 bytes total). Stored tag words
12..13 are excluded. The low then high 32-bit words hold the 64-bit result.
Verification compares both words by XOR/OR accumulation with no early return.
Shape validation is not authentication: the dispatcher must recompute the tag
in constant time and match the observed
TTBR0, active task generation, frame address, and monotonically increasing
sequence.

The scheduler initializes the boot key once from its entropy owner, copies it
into privileged-only storage, and volatile-wipes the exact 16-byte handoff
buffer on every path. All-zero, short, unavailable, or repeated initialization
fails closed and leaves the registry unusable. Each CPU has one
privileged-only active-token pointer; it is never placed in a user register,
user page, or user-readable vector literal. The SVC vector obtains the token
only through `arm32_token_lookup_active_v11(cpu_id)`. Registry ports are
bootstrap, issue, lookup, authenticate, advance, and revoke; issue fails if the
CPU already has an active token and revoke requires exact task and generation.

Each transition owns one 4-KiB SVC stack with an unmapped guard page directly
below it. `supervisor_sp` is its aligned top and `expected_frame_sp` is exactly
`supervisor_sp - 72`. SVC is non-reentrant: IRQ/FIQ remain masked from vector
entry until the complete frame and active token authenticate. A frame at any
other address is rejected.

The exact vector symbol is `arm32_vector_table_v12` in
`.vectors.arm32.v12`, 32-byte aligned and linker-retained before `.text.entry`.
VBAR rejects misaligned or out-of-kernel addresses. CPU identity is
`MPIDR.Aff0`; slots 0..3 are valid and all others fail closed.

The state machine is `PREPARED -> RUNNING -> EXITED -> REAPED`, with no reverse
or repeated transition. SVC 60 captures one bounded stdout byte from r0 for the
frozen probe payload and returns to User mode. SVC 0 accepts exit 37 exactly
once, changes the token to EXITED, restores kernel TTBR0 and the saved
supervisor continuation, then lets the scheduler reap the exact generation.
No page or L1 table is released before supervisor control resumes.

Any bad mode, root, tag, nonce, generation, frame pointer, sequence, syscall,
user address, output bound, exit code, or replay is a closed rejection and task
fault. It must never return through an unauthenticated supervisor address.

## v1.3 enabling owners and parallel ownership

The scheduler is the sole lifecycle-state owner. A per-CPU registry slot is a
kernel-only lease to one token; neither assembly nor the child owns the token.
The child receives only frozen read-only nonce bytes. SVC decoding produces a
bounded encoded disposition, which the scheduler validates and commits before
state, stdout, exit, reap, revocation, or table destruction changes.

User tables come from one static 1-MiB arena in `.arm32.user_tables.v13`,
aligned to 16 KiB and wholly kernel-identity-mapped: kernel address equals
descriptor physical address. Its 256-entry private ledger records address-
space ID, L1 index, kind, and span per 4-KiB page. L1 allocation consumes four
contiguous aligned pages; L2 allocation consumes one page. Pages are zeroed
before publish and again before ledger release.

The allocation-free fixed C port
`arm32_token_siphash24_v13(key[16], message[72])` follows the same SipHash-2-4
algorithm as the pure-Simple owner. Registry bootstrap requires canonical KAT
length 15 = `a129ca6149be45e5`.

## v1.4 disposition and parent commit

`Arm32SvcDispositionV14` is a fixed 64-byte scalar result containing action,
status, stdout byte, exit code, fault code, task/generation, syscall sequence,
authenticated-token receipt, observed TTBR0, frame address, return PC, SPSR,
and two required-zero words. Decode creates it without mutating token state.
The receipt is the current token MAC; the scheduler revalidates every identity,
root, frame, mode, sequence, receipt, and payload field before commit.

STDOUT commit accepts one byte, increments sequence, retags, and returns User.
EXIT commit accepts only 37, changes RUNNING to EXITED, increments/retags, and
resumes the supervisor continuation. Replay fails on stale sequence/receipt.
The parent owns a 256-byte per-CPU capture; overflow rejects before mutation.
After supervisor resume, `arm32_scheduler_reap_v14` requires the exact task and
generation, advances EXITED to REAPED, destroys the inactive address space,
then revokes and zeroes the token lease.

## v1.5 frame and kernel guard ownership

User data frames come from a separate bounded 4-MiB aligned arena and ledger.
The kernel identity maps the arena, zeros frames before allocation and release,
and stages validated ARM ELF32 `PT_LOAD` segments with W^X map flags. User and
SVC stacks have distinct backing frames.

The kernel guard owner replaces exactly one identity-mapped 1-MiB section with
an L2 table of 256 small pages, preserving AP, XN, TEX/C/B, S, nG, and domain
semantics, then leaves the selected 4-KiB PTE invalid. A bounded lease records
the original section and allocated table. Restore validates that lease before
republishing the section and releasing the table. Publish and restore use
DSB, targeted TLB invalidation, DSB, and ISB.

`arm32_qemu_nonce_read_v15` returns validated frozen nonce bytes into a bounded
caller buffer without printing. Scheduler admission still requires a real
16-byte boot entropy owner before token issuance; timer-derived deterministic
material is not an acceptable MAC secret.

## v1.6 boot entropy owner

ARM32 QEMU admission uses one bounded modern virtio-mmio RNG owner. Discovery
examines at most 32 platform slots and accepts magic/version plus device ID 4
only. A one-descriptor queue accumulates exactly 16 bytes across at most 16
nonempty completions; zero, overrun, timeout, all-zero output, and unavailable
provenance fail closed. Queue and rejected key material are wiped.

The scheduler boot wrapper is the only consumer: it passes the key to token
registry bootstrap and wipes its stack copy regardless of success. QEMU owns
the `/dev/urandom` backend and explicitly attaches `virtio-rng-device`; timer
mixing is never an entropy fallback.
