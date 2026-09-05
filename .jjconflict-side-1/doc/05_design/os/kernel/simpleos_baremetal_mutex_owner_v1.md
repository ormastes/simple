# SimpleOS Bare-Metal Mutex Owner V1

## Scope

`src/os/kernel/net/thread_shim.spl` retains the hosted `spl_mutex_*` ABI while
replacing the bare-metal unconditional-success shim. The canonical mutable
state is one aligned 32-bit word in a fixed 256-word boot-lifetime arena.
`MutexHandle` copies are handles to that word, not copied lock state.

## State and transitions

- `0`: unlocked.
- `cpu_id + 1`: locked by that hardware execution owner.
- `0xffffffff`: destroyed and never reusable.

Try-lock is one acquire compare/exchange from zero to the caller's owner word.
Lock repeats that operation for at most 65,536 attempts and then fails closed.
Unlock is one release compare/exchange from the caller's exact owner word to
zero. Invalid, forged, misaligned, unissued, stale, contended, double-unlock,
cross-CPU unlock, and destroyed-handle operations fail.

The architecture boundary is the smallest unavoidable unsafe leaf: x86 uses
locked `cmpxchg` and the full CPUID x2APIC identity when available; AArch64
packs MPIDR Aff3/Aff2/Aff1/Aff0; ARM32 uses the implemented MPIDR affinities and
`ldrex`/barrier/`strex`; and RISC-V uses `lr.w.aq`/`sc.w.rl`. Policy, bounds,
non-reuse, and failure behavior remain Pure Simple.

## Lifecycle constraints

Creation is serialized boot control-plane work. It must finish before
secondary cores or interrupts can call the shim. The arena allocator is not a
concurrent allocator. Destroy is terminal and storage is not reclaimed because
published scalar handles can outlive their creator; non-reuse prevents ABA.

The V1 execution identity is a CPU/hart ID, not a scheduled task ID. A task
must not migrate while holding this mutex. An interrupt handler must never call
blocking `lock`, because the interrupted context may own the same word; it may
only call `try_lock` and must tolerate false. An interrupt on the same CPU must
not unlock a lock acquired by the interrupted context. A future preemptive,
migrating scheduler requires a scheduler-issued execution token in the lock
word before that behavior can be claimed. RISC-V boot pins `tp` to the incoming
firmware hart ID before module initialization; V1 therefore also forbids later
repurposing `tp` as a per-CPU address. The x86 legacy-APIC fallback is valid only
for topologies whose firmware exposes unique 8-bit APIC IDs; x2APIC-capable
machines use CPUID leaf `0xB`'s full ID.

## Static acceptance cases

1. Two copied handles address the same word; only one zero-to-owner CAS wins.
2. A second try-lock while held returns false.
3. Unlock by another CPU, double unlock, and unlock after destroy return false.
4. Destroy while held does not alter the lock; destroy while unlocked is
   terminal; no slot is recycled.
5. Capacity exhaustion returns handle zero without writing outside the arena.
6. Every architecture provides acquire on successful lock and release before
   successful unlock/destroy publication.

Runtime/QEMU evidence is intentionally not claimed in this change.
