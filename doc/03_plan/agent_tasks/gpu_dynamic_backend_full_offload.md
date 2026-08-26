# GPU Dynamic Backend and Full Offload Agent Tasks

- Dynamic-loader/runtime owner: primary Codex; owns provider registry and native
  fixtures.
- SSpec/manual lane: primary Codex; manual generation remains blocked until an
  admitted pure-Simple Stage4 runner exists.
- Vulkan/CUDA physical evidence: existing backend lane owners; do not replace
  missing CUDA probes with fixture evidence.
- Metal physical evidence: prepared macOS owner; native raw readback remains
  required.
- Web/DB execution and profiling: existing GPU web/DB lane owner.
- Merge owner: primary Codex.
- Final reviewer: highest-capability Codex after every native row and generated
  manual are available.
- Lower-model sidecars: N/A for this focused runtime repair; broad umbrella
  completion retains the cooperative plan in the SPipe state.
