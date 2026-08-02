# NFR: SimpleOS Vulkan/CUDA/Adreno and Knowledge Routing

Selection: NFR Set 1, chosen by the user on 2026-08-02.

- NFR-001: Native backend promotion requires positive stable device identity
  and handle, correlated submission/fence/readback IDs, device-origin bytes,
  and exact CPU-oracle parity.
- NFR-002: Backend names and evidence classes are truthful. CUDA must never be
  reported as Vulkan; host offload must never be reported as guest-native.
- NFR-003: New owned decision points shall have at least 80% branch coverage,
  measured by a decision inventory or explicitly reported as unmeasurable when
  the runner cannot attribute source branches.
- NFR-004: Capability probing occurs once per device generation; hot submission
  paths perform no full-tree scans, driver probe subprocesses, or backend
  reinitialization.
- NFR-005: Device reset/loss, firmware or driver change, protocol change, and
  stale generation invalidate cached capability and receipt state.
- NFR-006: Knowledge selection is deterministic across hosts and agents; its
  receipt records registry version, selected stable IDs, content hashes,
  matched paths, and architecture profile.
- NFR-007: Missing hardware, external libraries, firmware, or toolchain support
  is reported as blocked/unsupported and never converted into a passing result.
- NFR-008: New source and process files comply with the 800-line maintainability
  limit, direct-runtime boundary guard, duplicate checks, and SPipe stub guard.
- NFR-009: Protocol-admission evidence is structural evidence only. Successful
  virtio-gpu feature, capset, context, resource-blob, or command-layout
  validation shall not be reported as command submission, Vulkan execution,
  fence completion, presentation, or device-origin readback evidence.
