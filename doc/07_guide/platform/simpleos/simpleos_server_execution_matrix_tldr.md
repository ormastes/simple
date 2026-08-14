# SimpleOS server execution matrix — TLDR

Required rows are real ARM64 QEMU CPU, physical UNO Q CPU, and physical UNO Q
Adreno/Vulkan, plus honest Linux CPU/optional-GPU comparison rows. Each target
must filesystem-launch current server bytes and retain a
`SimpleOsServerExecutionReceiptV1`; substitutions fail closed. ARM source
prerequisites advanced and the storage/QEMU preflight passes, but persistence
and current-source ARM compiler/sysroot/runtime blockers prevent execution credit. UNO Q has identity-only
Debian evidence, not a SimpleOS run. The executable SSpec and authored mirror
keep every missing row explicitly red; neither runtime nor docgen was run.
