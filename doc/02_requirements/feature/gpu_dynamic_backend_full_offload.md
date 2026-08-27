# GPU Dynamic Backend and Full Offload Requirements

Selection: **Option A — versioned function table with owned sessions**.

## Requirements

- REQ-GPU-DYN-001: The host shall admit a GPU provider only through one
  exported ABI-v1 query entry point returning a size/version/backend/capability
  checked function table.
- REQ-GPU-DYN-002: The table shall expose opaque provider, session, resource,
  and completion handles plus create/destroy, submit, wait, readback, typed
  error, and backend-operation discovery contracts.
- REQ-GPU-DYN-003: Provider admission shall be atomic and fail closed for a
  missing query, wrong ABI, undersized table, mismatched backend bits, missing
  required capability, or null required function.
- REQ-GPU-DYN-004: A compatible provider may be installed or replaced after
  quiescence without rebuilding or relinking the deployed Simple executable.
- REQ-GPU-DYN-005: Public Simple callers shall use the shared provider/session
  facade. CUDA, Vulkan, and Metal remain implementations below ProcessingIR and
  DrawIrComposition, not public API forks.
- REQ-GPU-DYN-006: Provider calls shall return typed status values. Missing,
  rejected, timed-out, or failed providers shall never abort the process or be
  reported as successful GPU execution.
- REQ-GPU-DYN-007: A GPU execution claim requires submission, completion,
  positive provider/session/device identity, device-origin readback, and exact
  CPU-oracle parity. Synthetic handles and CPU mirrors are invalid evidence.
- REQ-GPU-DYN-008: Vulkan shall execute the canonical Simple2D, WebIR-to-DrawIR,
  GUI, and WM compositions through Engine2D with retained device evidence.
- REQ-GPU-DYN-009: CUDA and Metal shall execute the same representative Draw IR
  fixtures with exact readback parity and failure/recovery evidence on their
  native hosts.
- REQ-GPU-DYN-010: Web and DB GPU work shall be coarse-grained ProcessingIR
  batches. Networking, parsing, routing, backpressure, durability, transaction
  commit, and invalidation remain CPU-owned.
- REQ-GPU-DYN-011: Web/DB GPU promotion shall require verified device execution,
  CPU parity, bounded queues/resources, and measured benefit over the CPU path.
- REQ-GPU-DYN-012: Profiles shall separately measure producer/function-call,
  IR construction, IR marshaling, backend submission, device execution,
  synchronization, readback, and end-to-end lanes.
- REQ-GPU-DYN-013: Native-host rows unavailable on the current machine shall
  remain open and fail closed with a TODO and exact resume command; they shall
  not be converted to skips or completion evidence.

## Traceability

The acceptance mapping and commands are maintained in
`doc/03_plan/sys_test/gpu_dynamic_backend_full_offload.md`. Existing selected
renderer, ProcessingIR, Metal, and web/DB requirements remain additive.
