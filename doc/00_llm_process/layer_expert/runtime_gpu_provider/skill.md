# Runtime GPU Provider Layer Expert

## Ownership

`src/runtime/runtime_dynload.c` owns hosted GPU provider open/query/lease/close.
`src/runtime/simple_gpu_provider_abi_v1.h` is the cross-toolchain ABI. Pure
Simple callers must use an owner facade; app-local `rt_*` aliases and direct
provider-table access are forbidden.

## ABI rules

- Use fixed-width integers, explicit struct sizes, opaque `u64` handles, and
  positive stable provider/device identities.
- ABI major mismatch, newer unsupported minor, short table, missing capability,
  null required callback/operation, or backend mismatch is unavailable.
- Providers expose the query only. Backend functions may have hidden linkage
  and are reached through table operation slots.
- Never hold the registry lock across provider code. Acquire a lease, call,
  release; reject unload until calls and owned sessions quiesce.
- Compatible replacement occurs after quiescence through the same unchanged
  host executable. Never silently fall back to a global symbol of the same name.

The focused authoritative test is
`scripts/check/check-gpu-provider-dynload-registry.shs --intensive`; native GPU
readback and Tier-3 profiles are separate evidence rows.
