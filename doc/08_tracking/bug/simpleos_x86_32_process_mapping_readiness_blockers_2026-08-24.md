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

Until those owners join the scheduler transaction,
`executable_target_dispatch_v1` must retain
`process_image_builder_ready = false` for canonical architecture `x86`.
