# Metal MSL Processing Backend Agent Tasks

- Lane owner: `metal_msl` Codex agent.
- Shared-contract owner: `vulkan_llvm` agent; Metal consumes its public types
  without editing the shared file.
- Lower-model sidecars: N/A; scope is a narrow independent lane.
- Merge owner and final normal/highest-capability reviewer: root Codex agent.
- Frozen interfaces, step text, and checker helpers are those recorded in
  `.spipe/gpu_renderer_processing_backends/state.md` and the detail design.
- Native macOS execution owner: prepared-macOS evidence operator; final reviewer:
  root Codex agent.
