# SimpleOS x86-32 process mapping readiness blockers — 2026-08-24

The authenticated ELF32/i386 metadata path is present, but filesystem-launched
x86-32 execution must remain blocked before loader authority consumption.

- `stack_builder.build_initial_stack_checked` accepts only `abi_word_size == 8`
  and emits eight-byte argc, pointer, and auxv slots. The x86-32 System V ABI
  requires a bounded four-byte serializer with 16-byte entry alignment.
- `arch/x86_32/paging.spl` creates two-level process page directories but its
  map/unmap/translate calls use only `g_vmm.pd_phys`. The scheduler adapter
  instead calls the x86-64 PML4 explicit-root implementation for `@cfg(x86)`.
- No x86-32 owner currently rolls back partially mapped leaf frames and private
  page tables or destroys a process page-directory tree on every failure.
- Three static design/review cycles rejected an attempted explicit-root owner.
  The remaining safe design requirements are: an authoritative create-issued
  root and unique-leaf registry; duplicate physical-frame aliases must be
  rejected; map and destroy must serialize; every fallible lock/unlock boundary
  must end in a retryable `Active`, `Released`, or `Quarantined` state; a
  teardown that already freed the tree must never report a retryable failure;
  and every quarantine path must return an owner/lease rather than orphaning
  the root. The unsafe draft was reverted.
- Classic two-level non-PAE i386 has no NX bit. A future mapping receipt must
  not claim writable-vs-executable hardware isolation without a selected
  PAE/NX policy or an explicitly accepted non-NX security row.
- A consume-once scheduler adoption must transfer the future mapping owner into
  a task, install its CR3 for CPL3 entry, and invoke terminal destruction.

Until those owners join the scheduler transaction,
`executable_target_dispatch_v1` must retain
`process_image_builder_ready = false` for canonical architecture `x86`.
