# SimpleOS server execution matrix — TLDR

Required rows are real ARM64 QEMU CPU, physical UNO Q CPU, and physical UNO Q
Adreno/Vulkan, plus honest Linux CPU/optional-GPU comparison rows. Each target
must filesystem-launch current server bytes and retain a
`SimpleOsServerExecutionReceiptV1`; substitutions fail closed. ARM source
prerequisites, target sysroot/runtime, RecoverableReplaceV1, and the structural
SARD capability probe are present, but the missing admitted current-source
Stage-4/full compiler prevents execution credit. UNO Q has identity-only
Debian evidence, not a SimpleOS run. The executable SSpec and authored mirror
keep every missing row explicitly red; neither runtime nor docgen was run.
Once a full CLI exists, admit it with
`scripts/check/admit-simpleos-arm64-server-compiler.shs`; Stage 2 and the Rust
seed cannot substitute for that receipt.
