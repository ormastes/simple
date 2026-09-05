# GPU provider registry exports missing

Status: claimed by the GPU dynamic backend/full offload lane on 2026-08-26.

## Exact reproducer

```text
sh scripts/check/check-gpu-provider-dynload-registry.shs
```

The harness link fails because `runtime_native.o` has no
`rt_gpu_provider_loaded`, provider metadata queries, or dynamically dispatched
CUDA/Vulkan operation exports. The adjacent Metal checker fails with the same
registry gap and missing Metal byte/value adapters.

## Ownership decision

- `runtime_need`: open a host library, bind a versioned native ABI, retain its
  handle, dispatch native GPU calls, and close it safely.
- `facade_checked`: `src/os/posix/dynlib.spl`, the stable provider-query wire,
  and existing GPU owner facades. Pure Simple correctly delegates host-library
  access; the missing behavior is below that boundary.
- `chosen_path`: runtime-owned change in `src/runtime/runtime_dynload.c`, the
  canonical host dynamic-loader owner.
- `rejected_shortcuts`: app-local externs, backend field pokes, fixture-only
  success, static provider linking, and CPU mirrors labeled as device work.

## Adjacent regression

The Metal provider checker is the adjacent case. It additionally proves that
embedded zero bytes and array RuntimeValues are decoded by core-owned adapters
rather than provider-specific Simple callers.

## Completion condition

Both focused provider checkers link and pass; wrong ABI, missing operation,
missing library, unload/reload, and absence of a static provider dependency
remain fail-closed.

