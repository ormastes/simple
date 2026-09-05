# x86-32 authenticated mapping owner v1

## Scope

The loader mapping capsule joins the authenticated ELF32/i386 layout evidence
to the explicit non-PAE page-root owner. It deliberately stops before scheduler
adoption: its receipt is not permission to load CR3 or enter CPL3.

## Ownership

The capsule is the sole owner of a bounded four-slot mapping registry. Each slot
retains its create-issued page-root lease and the exact virtual/physical leaf
coordinates. Input handles and source bytes are immutable copies. Page roots,
page tables, and leaf frames remain owned resources; public receipts are opaque
generation/nonce coordinates and never ownership transfers.

Preparation re-runs ELF parsing, exact PT_LOAD comparison, target validation,
source-size validation, and SHA-256 over the provided bytes before allocating a
root. It maps each page once, copies only the file-backed interval, verifies each
write, verifies the BSS tail is zero, and creates one bounded stack page. The
initial stack contains five little-endian four-byte zero words (`argc`, argv and
env terminators, and the `AT_NULL` pair), with a 16-byte aligned entry pointer.

## Permission honesty

Classic two-level non-PAE paging cannot enforce execute-disable. Writable
segments and the stack are writable, while other segments are read-only, but
all receipts report both `hardware_execute_disable=false` and
`hardware_wx_enforced=false`. This module must not be used to claim a W^X gate.

## Failure and teardown

Every registered leaf is retained before copy/readback. A later failure unmaps
leaves in reverse order, releases their exact frames, and destroys the still
unpublished root. Failed unmap leaves remain retained as retryable ownership;
an indeterminate root teardown is quarantined. Generation/nonce/state matching
rejects stale or copied lifecycle receipts. The mapping capsule admits at most
255 image pages plus one stack page. This sharp bound reserves stack capacity
and caps the lower owner's linear physical-provenance lookup rather than
advertising its much larger raw leaf ceiling as practical image capacity.
Exact PDE and PTE values are read back before successful publication; an
indeterminate PTE retains a quarantined leaf coordinate instead of succeeding.

## Remaining boundary

`x86_32_authenticated_mapping_scheduler_ready_v1()` remains `false`. A future
consume-once scheduler transaction must adopt the mapping slot, install and
restore CR3 around CPL3 execution, own kernel-stack/TSS state, and invoke
terminal mapping destruction on task reap before global x86-32 filesystem exec
can become ready.
