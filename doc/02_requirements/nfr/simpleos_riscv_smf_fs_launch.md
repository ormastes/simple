<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch NFRs

- NFR-RISCV-SMF-001: Host-side image validation must fail before boot if expected RISC-V SMF payload markers are missing.
- NFR-RISCV-SMF-002: Runtime validation must emit stable serial markers: `FS_MOUNT_OK`, `SMF_DISCOVERY_OK`, `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`, `NATIVE_GUI_PROCESS_RENDER_OK`, and `SIMPLEOS_RISCV_SMF_FS_PASS`.
- NFR-RISCV-SMF-003: The RISC-V acceptance lane must read full SMF files from FAT32, unwrap embedded ELF payloads, validate program headers, and copy PT_LOAD data into process-owned native arenas before reporting success.
