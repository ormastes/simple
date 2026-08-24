# SimpleOS ARM32 process mapping integration blocker — 2026-08-24

## Current safe prerequisite

The pure-Simple ARM32 readiness owner now binds an authenticated image handle to
the exact source digest, canonical `simpleos/arm/simpleos` dispatch row, shared
ELF32/EM_ARM parser result, exact PT_LOAD layout, user-address ceiling, bounded
page count, and reserved stack window. It executes before any authority token
transition and grants no execution authority.

## Exact remaining blocker

`executable_target_dispatch_v1` cannot safely mark ARM32 process images ready
until all of these owner transitions exist:

1. `process_image.spl` needs a 32-bit initial stack builder invocation using
   four-byte argc/argv/envp/auxv words and eight-byte ARM ABI stack alignment;
   its current shared builder rejects every 32-bit architecture.
2. The ARM32 PT_LOAD address-space portion now has an isolated explicit-root
   map/copy/zero-fill/readback owner with bounded reverse rollback and retryable
   quarantine. The remaining address-space gap is the initial stack: it needs
   a 32-bit builder and must be mapped into the same owned root before adoption.
3. Scheduler executable adoption must compare the active ARM32 architecture,
   consume the joint loader reservation exactly once only after preparation,
   commit the mapped address space and TCB through the canonical scheduler
   owner, and preserve retryable source-close state after publication.
4. Static and QEMU acceptance must prove an authenticated filesystem-backed
   ARM ELF reaches user mode and that malformed/digest-stale/layout-stale inputs
   fail before authority consumption. Runtime evidence was explicitly excluded
   from this change, so no such claim is made here.

Until those items land together, the canonical dispatch row must remain false;
changing it earlier would let load-plan and joint-reservation gates consume an
authority that no production ARM32 mapper can finish safely.

## 2026-08-24 static implementation update

`src/os/kernel/arch/arm32/user_page_table_owner_v1.spl` now binds the armed
identity and authenticated load plan before allocating a PMM-owned, explicit
ARM32 short-descriptor root. It owns PT_LOAD frames and L2 tables, performs
copy/zero/readback, and retains residual resources after partial rollback.
No test, build, SPipe, benchmark, optimizer, bootstrap, or runtime verification
was run for this update, so it does not establish ARM32 execution readiness.
