# ARM32 authenticated process mapping readiness v1

## Scope

`executable_arm32_mapping_owner_v1.spl` is a bounded, non-authorizing owner for
ARM32 mapping preparation. It accepts only an already-authenticated
`ExecutableImageHandleV1` plus the exact retained source bytes. It routes the
handle through canonical `executable_target_dispatch_v1`, requires the exact
`simpleos/arm/simpleos` target, re-hashes the source, and reparses it through the
shared ELF owner as ELF32/EM_ARM.

A positive candidate receipt proves only that the copy-only input is structurally ready
for a future ARM32 mapper. It contains no open handle, address space, loader
token, scheduler handle, or mutable lifecycle state. The package-facing boolean
is intended to run before joint reservation or token consumption.

## Bounds and ownership

- Source bytes are limited to 64 MiB and are hashed without making a second
  image copy.
- ELF parsing admits at most 64 authenticated PT_LOAD ranges. Each parsed range
  must exactly match the handle's signed/admitted range record.
- Page planning is bounded to 65,536 4-KiB pages. Pairwise page-alias checking
  is O(n²), with n capped at 64; no unbounded map or cache is allocated.
- All mapped pages must remain inside canonical ARM32 user address policy and
  outside the exact stack reservation derived from `ARM32_USER_STACK_TOP` and
  the shared `compute_stack_size(source_size)` policy.
- The loader registry remains sole owner of one-shot authority. The scheduler
  remains sole owner of address spaces and runnable task publication.

## Fail-closed integration state

The package-facing gate additionally binds a loader-owned Armed identity and a
fresh exact ARM consumer to the handle, entry, source, and structural receipt.
Its receipt always reports `authority_consumed = false` and
`process_image_ready = false`; publicly constructible handle values alone are
never described as authenticated authority.

The Armed identity is a bounded copied snapshot and can become stale immediately
after it is issued. This preflight checks internal snapshot/handle consistency;
it does not prove the registry slot is still Armed. Any future authorizing
transition must atomically revalidate the slot generation and nonce and consume
the live registry state through the registry owner.

Canonical dispatch deliberately retains
`process_image_builder_ready = false` for `arm`. The readiness owner does not
claim that ARM32 pages can currently be mapped or rolled back. Enabling global
dispatch requires the integration items recorded in the companion blocker.
