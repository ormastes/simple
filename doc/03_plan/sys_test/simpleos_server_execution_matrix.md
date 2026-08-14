# System test plan: SimpleOS server execution matrix

Trace the frozen steps/helpers in `.spipe/simpleos_server_execution_matrix/state.md`.

1. REQ-001..003: ARM boot, VFS launch, HTTP file, DB write/read and fresh-boot
   persistence.
2. REQ-004..007: physical UNO identity/hash, VFS launch, protocol restart,
   forced CPU-only, then Adreno/Vulkan submit/completion/readback.
3. REQ-008..011: equivalent Linux CPU rows, optional CUDA compute row, dynload
   absence in CPU mode, and before/after optimization evidence when required.
4. REQ-012: deliberate-red rejection of marker, host substitution, missing
   receipt fields and GPU fallback.

No scenario may use an empty body, placeholder pass, or unretained observation.
