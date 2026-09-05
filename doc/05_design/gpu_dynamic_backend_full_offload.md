# GPU Dynamic Backend and Full Offload Detail Design

## Provider state

Each backend slot stores its backend bit, environment-facade-owned path key,
attempted state, admitted handle, ABI version, capability bits, and copied path.
The loader resolves metadata first, validates the complete backend surface, and
publishes the handle only after every check succeeds. Failure closes the
candidate and clears all metadata.

## Dispatch adapters

Scalar CUDA/Vulkan calls forward through typed function pointers resolved from
the admitted local handle. Metal text and array calls remain core-owned adapters:
strings use explicit data and length, input arrays validate every byte, output
arrays are updated only after a successful provider call, and temporary buffers
are released on every path.

## Failure behavior

Missing or rejected providers return existing backend-unavailable sentinels.
No operation falls through to a similarly named global symbol. Unload of an
unknown backend fails; unload of a known slot is idempotent and resets admission
so the next operation observes the newly configured path.

## Tests

The native fixture builds complete, wrong-ABI, incomplete, missing, and
replacement providers. It checks actual calls, zero-byte payloads, 8 concurrent
readers with 100 iterations each, unload/reload, changed results from the second
provider, and no static provider dependency. The mirrored modern SSpec is
`test/03_system/runtime/gpu_provider_dynamic_load_spec.spl`.

