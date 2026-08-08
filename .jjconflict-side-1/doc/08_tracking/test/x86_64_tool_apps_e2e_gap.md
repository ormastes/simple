# x86_64 Tool Apps Serial Marker — Contract-to-QEMU Gap

`src/os/x86_64_fs_loaded_marker_contract.spl` defined `tool_apps_serial_accepts_completion()`
(requiring `process-backed:ok`/`vfs-app-read:ok` markers for `/sys/apps/simple_compiler`,
`simple_interpreter`, `simple_loader`) with zero callers repo-wide — an aspirational contract,
never run against a real boot.

`test/03_system/os/port/x86_64_tool_apps_serial_e2e_spec.spl` now wires it into the real
`x86_64-q35-nvme-fat32-smf` fs-exec acceptance lane (kernel `build/os/simpleos_x86_64_fs_exec.elf`,
image `build/os/fat32-x86_64.img`), gated on `SIMPLEOS_QEMU_SMOKE=1` like its sibling
`e2e_qemu_smoke_spec.spl`.

Unblocks when: (1) Phase-1 in-guest exec lands so `examples/09_embedded/simple_os/arch/x86_64/fs_exec_entry.spl`
stages and launches `simple_compiler`/`simple_interpreter`/`simple_loader` as real processes, and
(2) a real SimpleOS-target `simple` binary is built and staged as those three `/sys/apps/*` entries.
Until then the gated-on run is EXPECTED RED (fails closed, never a skip).

Caveat observed while wiring this: in the current `bin/simple test` interpreter runtime,
`rt_env_get` does not observe the host process environment inside `it` blocks, so
`SIMPLEOS_QEMU_SMOKE=1` cannot currently flip the gate on via `bin/simple test` in this
sandbox (pre-existing, shared by `e2e_qemu_smoke_spec.spl`'s identical gate — not introduced
by this change). Compiled-mode / container test execution is expected to read it correctly.
