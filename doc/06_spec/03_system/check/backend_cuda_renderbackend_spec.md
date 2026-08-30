# CUDA RenderBackend batching

Executable companion:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`.

`step("Submit one backend batch and read device pixels")` invokes
`expect_backend_batch_receipt` when CUDA initializes. The helper verifies two
pending image resources, one successful batch synchronization, a cleared
pending-resource list, and exact `device_readback` pixels. On an unavailable
CUDA host the test instead asserts that the backend is not initialized; it does
not promote that branch into device-execution evidence.
