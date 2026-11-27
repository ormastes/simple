# ARM32 authenticated syscall adapter

Status: native full-frame owner, published mapping checked-copy transaction and
private moved-owner context exist as source. No guest qualification.

The default `exception_vectors.s` now passes the actual saved r0-r12 and return
PC to `rt_arm32_svc_dispatch_frame_v1`. A returned syscall value replaces saved
r0 before the vector restores registers. The blocking entry saves 40 bytes so
the SVC stack retains AAPCS eight-byte alignment. The v14 fixture remains
unchanged and cannot count as tool execution.

The native mode-2 prototype requires a real strong Simple dispatcher probe,
an exact task/generation/root tuple, and an actual frame at the retained SVC
stack position. It rejects nesting and non-BSP or interrupt-enabled entry.
Each accepted dispatch consumes a nonreused epoch. A syscall result must fit
the ARM32 signed register return. Native completion requires the Simple exit
handler to return success; failed exit cleanup returns an error to the child.

The existing scalar token install/reap C ABI previously accepted 64-bit
RuntimeValue arguments while `user_entry.spl` declared 32-bit words. Those
functions never decoded or boxed values. Their C declarations now match the
existing SPL declarations exactly: `(u32,u32)->i32` and
`(u32,u32,i32)->i32`. Actual ARM LLVM definitions and a sentinel C caller
confirm the fixed signatures; a generated Simple caller remains unverified.

## Ownership boundary still required

The canonical TCB mapper is `user_page_table_owner_v1.spl`, whose live slot
owns its PMM leaves, L2 identities and root. The new copy transaction validates
the exact published mapping handle, lifecycle and native epoch under that
owner's mutex. It checks the actual L1/L2 descriptors against owned table and
leaf identities before I/O. At most 17 covered pages are checked for a 64 KiB
request. Copying uses the validated user VA under the still-active child TTBR,
avoiding an additional physical cache alias for the guest's data.

The private architecture context obtains that handle from the actual moved
Scheduler/IPC aggregate. No unbounded native page-table walk or guessed RAM
window is permitted. The earlier unused native legacy-arena byte/range exports
were removed when this canonical transaction was implemented.

The context consumes `AuthenticatedUserSyscallOwnersV1` once and returns the
mutated owners through the frozen neutral result boundary. Indeterminate
cleanup retains the real owners privately. Its strong dispatcher delegates
ordinary operations to the shared core, inherits the real parent's FD/OFD
state and arms the canonical capture only after the native handshake. A
single-use route receipt must gate the external evidence-delivery path;
reason strings and a numeric zero exit never qualify output. Unsupported
operations poison that receipt. Owner uncertainty returns an out-of-register-
range sentinel, forcing the native frame owner to reject further execution.

The actual boot caller, selected strong export/link-provider closure and FD32
SDK profile remain unverified or absent. An explicit fresh provisional FD32
SDK/tool profile can be built for real diagnostics; its execution supplies the
qualification evidence rather than requiring that evidence before the build.
The default legacy profile remains unchanged and unqualified. No flag may
label the current source a working tool runner.

## Anonymous memory owner

Syscall 10 is handled by the architecture context only when the actual moved
IPC owner grants `VmMap`. Its published mapping capsule also requires the
opaque exact-child anonymous policy and a nonzero finite page allowance.
Allocation reserves the page ledger before PMM allocation and owns every
frame and rollback receipt in that same serialized capsule. New pages are
zeroed, mapped with read-only or read/write user permissions and XN, and their
page-table/cache/TLB publication finishes before a user address is returned.
File-backed, shared and fixed mappings remain rejected by the actual libc
boundary. Unsupported protection modes return an explicit error.

The independent anonymous allowance is not signed total memory, RSS or a
capacity promise. The private user VA window is finite, and selection checks
real mapping emptiness, original load runs and the policy's stack/guard bounds.
The region bound is 4096 to match the selected `simpleos_dlmalloc.c` owner;
that provider already records a real workload failure at its former 256-region
cap. Its free list does not invoke syscall 11. Other callers of unsupported
memory operations invalidate capture instead of receiving a fake success.

Exit retires anonymous frames before descriptor cleanup and Scheduler exit.
Only an exact owned PTE can be cleared; cache publication and TLB invalidation
precede release. The sole release record is cleared before the valid-frame
PMM call. Charges refund only after all owned mappings are proven gone;
partial rollback retains the actual frames and complete reservation. Root
destruction refuses outstanding anonymous charges. No PMM frame or kernel
section can be freed by copying a receipt or passing a raw root.

Copy lookup uses immutable contiguous load-run indices plus a binary search
over monotonically ordered anonymous regions. It does not scan every frame
for each byte/page. Actual startup, syscall latency and max RSS on realistic
fixtures remain pending the real kernel/tool build and guest campaign.

## Actual kernel continuity and cache publication

The ARM32 linker places the kernel at `0x40000000`, below the old mapper's
high-half-only copying rule. The mapper now borrows only unchanged ordinary
supervisor-only sections from its actual parent root, including low kernel
and device sections. It never borrows a coarse table or frees a borrowed
section target. User mappings retain the existing section-collision rejection.

Native preflight runs before switching roots. It checks actual CPU TTBCR,
SCTLR, DACR, MPIDR, mode and interrupt state; manager domains and unsupported
translation, endianness or section encodings fail closed. The admitted ABI is
ARM state with software floating point; CP10/CP11 access must be disabled,
since this frame does not preserve optional VFP registers. It compares both
roots for the real linker kernel interval, live vector and stack, and all
borrowed supervisor sections. Missing or coarse parent regions are refused.
The copied descriptors retain their physical targets and cache/XN/domain bits.

The canonical page owner cleans its exact root, L2 tables and image leaves
under its mutex and publishes instructions before entry. This is necessary
because the existing paging initializer enables both data and instruction
caches. It does not disable caches or assume a coherent QEMU shortcut.

## Retained evidence

`build/verify/arm32-authenticated-svc-v1/` contains:

- Whole real ARM32 C and both assembly target compiles, successful.
- 24 actual owner-body controls executed under mocked native state, successful.
- 11 additional actual range-body controls, successful.
- 12 actual native section-preflight controls, including manager-domain and
  absent-low-kernel negatives, successful.
- ARM32 LLVM provider definitions and fixed-width sentinel C caller, successful.

The earlier legacy-arena prototype's 24 owner/copy and 11 range controls are
historical evidence only; those copy exports are no longer part of the adapter.
The newer coarse-domain, widened-span, identity-RAM and installation rejection
controls remain unexecuted. They cannot verify the uncompiled SPL copy/VM owner.

The four edited/new SPL production files passed official primitive/nil delta
checks before the anonymous-owner addition. Its changed owner/context sources
require a final delta check after review. Four direct section-clone SPL unit
scenarios exist but are unexecuted.
Seven direct publication-decision scenarios are also authored and unexecuted.
The 22 new CPU provider instruction strings assembled for the real ARM target;
that syntax object is explicitly not a kernel provider or Simple codegen proof.
The user memory fixture compiled to an ARM target object without execution.

Host controls do not execute CP15 instructions, exception return, a kernel or a
guest. The new SPL source is uncompiled. Three reported VM/Simple ownership
findings cleared dedicated Astra source review; this is no runtime admission.

Native accounting was corrected to include source-review/fix batches. The
previous five-build-batch count omitted them: coarse-domain correction was
cycle six, and two further native source corrections occurred before the
accounting mistake was recognized. Native edits, builds and retries are now
stopped. The current native inputs are uncompiled and unqualified. An explicit
user override is required before further native work, including a hardware
build intended to verify these changes. The tracked stop report pins current
inputs and retained historical artifacts without restamping their old passes:
`doc/08_tracking/bug/simpleos_arm32_authenticated_native_cycle_limit_2026-11-24.sdn`.

The separate SPL ownership work has five source verification/review-fix batches;
its final batch requires a proper producer and cannot substitute native proof.
# Approved native extension evidence (2026-11-24)

The original six-cycle ledger and the two source batches incorrectly performed
after that limit remain recorded in
`doc/08_tracking/bug/simpleos_arm32_authenticated_native_cycle_limit_2026-11-24.sdn`.
The user subsequently approved exactly two additional native cycles. Both are
now consumed; this does not reset the separately tracked SPL ownership budget.

Extension 1 added independent privileged ATS1CPR/PAR checks before dereferencing
any current, parent or candidate root table as an identity virtual address.
Each of the four root pages must translate to its own physical page. Faults and
supersection translations are rejected, and the prior PAR value is restored.
Astra cleared that repair at source level. The actual ARM C source, both entry
assembly files and fixed-width C provider/sentinel-caller LLVM ABI checks passed.
The host controls failed before execution because the initially selected host
compiler lacked `stdio.h`.

Extension 2 ran only the four previously unexecuted host groups with the installed
MinGW toolchain: owner 20, preflight 16, translation 18 and install-negative 4.
All 58 controls passed; the source snapshots remained unchanged. It did not
repeat the passing target or ABI checks. Exact inputs, compiler identity,
commands and outputs are retained under
`build/verify/arm32-authenticated-svc-v1/extension1` and `extension2`.

The verified C input SHA256 is
`9e06a70cce535d2a7f07095cccd98dcd072c894a7d43737e7153ebaade32c013`.
These are target-compilation and host-mock observations only. They do not prove
the actual generated Simple caller/provider ABI, a linked kernel, guest
execution, capture admission or any lint/test matrix row.

