# Metal backend primitive batching

Executable companion:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_batch_spec.spl`.

`step("Submit one backend batch and read device pixels")` invokes
`expect_backend_batch_receipt`.

This host-independent source contract keeps the retained primitive encoder,
flush-before-submit order, completion handling, and image-boundary failure
paths visible. Exact Metal device pixels and counters require a macOS Metal
host, so this specification does not claim hardware execution on other hosts.
