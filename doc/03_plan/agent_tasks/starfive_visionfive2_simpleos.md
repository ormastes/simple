<!-- codex-design -->
# StarFive VisionFive 2 SimpleOS agent tasks

- Primary interfaces and manual vocabulary: defined by root Codex before fan-out.
- Source architecture sidecar: `/root/starfive_design_src`, merged findings accepted.
- SPipe/manual sidecar: `/root/starfive_design_test`, merged findings accepted.
- Host tooling sidecar: `/root/starfive_design_tools`, merged findings accepted.
- Merge owner: root Codex.
- Final reviewer: root Codex at best available model capability; verify must independently assess done marks and exclusions.

Implementation order: fix generic RamFs/VFS owner defects; add board/catalog/entry/linker and immutable packaged root; add safe build/JTAG/UART/SBI-reset tooling; add executable/manual system evidence; update SPipe knowledge and operator guide; verify, commit, and push.
