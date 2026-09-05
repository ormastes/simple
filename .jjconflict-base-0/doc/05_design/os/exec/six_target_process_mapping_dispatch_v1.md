# Six-target process mapping and dispatch policy v1

## Scope

`executable_target_dispatch_v1.spl` is a pure routing prerequisite between the
authenticated installed-artifact admission path and the loader/scheduler
owners. It recognizes exactly `x86_64`, `x86`, `aarch64`, `arm`, `riscv64`, and
`riscv32` for the `simpleos/simpleos` OS/ABI pair.

It does not mint authority, open a path, retain image bytes, allocate an address
space, or publish a task. Loader joint reservation still requires the exact
armed token, canonical source path, entry identity, and matching fresh consumer.
Scheduler adoption additionally compares the policy architecture with the
active kernel architecture before process-image preparation.

## Ownership and bounds

- Installed-artifact catalog: sole owner of authenticated path/target records.
- Loader authority registry: sole owner of the one-shot image/token state.
- Scheduler: sole owner of mapped address spaces and runnable task publication.
- Dispatch policy: immutable copy-only target metadata; never an authority.

The policy centralizes pointer width, user-address ceiling, and stack alignment.
Lookup is constant time with six exact cases and allocates no collection.

## Honest readiness

ELF admission already recognizes all six targets. The 64-bit process-image
builder is present for x86-64, AArch64, and RV64. The 32-bit policy rows are
recognized for exact non-authorizing routing but retain
`process_image_builder_ready = false`. Load-plan validation, loader joint
reservation, and scheduler pre-commit dispatch reject those rows, preserving
the one-shot token until a correct 32-bit initial-stack builder and mapper
exist.

No catalog population fallback is introduced. A path or target policy alone
cannot reach mapping or scheduler publication.
