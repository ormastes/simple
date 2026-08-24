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
2. The ARM32 address-space owner needs an actual map/copy/zero-fill/readback path
   for the admitted PT_LOAD pages and initial stack, plus complete rollback that
   destroys every allocated page on partial failure.
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
