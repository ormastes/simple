<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Smoke NFRs

- NFR-RISCV-SMF-001: Host-side image validation must fail before boot if expected RISC-V SMF payload markers are missing.
- NFR-RISCV-SMF-002: Runtime validation must emit stable smoke markers: `FS_MOUNT_OK`, `SMF_DISCOVERY_OK`, `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`, `NATIVE_GUI_PROCESS_RENDER_OK`, and `SIMPLEOS_RISCV_SMF_FS_PASS`.
- NFR-RISCV-SMF-003: The RISC-V smoke lane must not emit desktop process-backed ownership markers; hosted proof belongs to the separate `riscv64-hosted` lane.
