# aarch64-apple-darwin Hosted Lane Design

**Feature:** #QEMU-SYSTEST-MULTIARCH-AC7
**Lane 7 of 7** in the SimpleOS multiplatform systest suite.

## Hosted vs bare-metal

The six existing lanes (x86_64, x86_32, arm64, arm32, riscv64, riscv32) all:
- Build freestanding ELF kernels linked against a custom `linker.ld`
- Boot inside QEMU virtual machines
- Print acceptance markers to a UART serial line
- Use `spl_start()` as entry point with `rt_qemu_exit_success()` to terminate
- Use `serial_println()` for all output

The aarch64-darwin lane is fundamentally different:
- Builds a native **Mach-O** binary for `aarch64-apple-darwin`
- Executed **directly** by the test runner as a child process (no QEMU)
- Output goes to **stdout** (captured by `rt_process_run_timeout`)
- Entry point is `fn main()` (darwin runtime convention)
- No linker script (ld64 handles darwin binaries natively)
- No `-nostdlib`, no `-ffreestanding`, no `-static` link flags
- Uses standard host-FS externs (`rt_file_exists`, `rt_file_read_bytes`)

## Why `run_qemu_systest` is reused

The `run_qemu_systest` helper in `qemu_systest_contract.spl` is a generic
process-runner: it checks two file paths (binary + app file), spawns a process,
captures stdout+stderr, and calls `classify_serial` on the result.

For the hosted lane:
- `kernel_path` → `build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` (the binary)
- `image_path` → `build/os/darwin-aarch64/hello_world.smf` (the staged app)
- `qemu_bin` → `build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` (run the binary directly)
- `qemu_args` → `[]` (no extra args; the binary reads app_path from a hardcoded constant)
- `timeout_ms` → 15000 (15s; much faster than QEMU boot)

The name "qemu_systest" is a misnomer for this lane — it is a generic
process-launch-and-classify primitive. The doc notes this honestly.

## Honest marker set

Each marker asserts a **real capability** the hosted process actually exercises.

| Marker | What it asserts | Why honest |
|--------|-----------------|------------|
| `HOSTED_FS_READ_OK path=... bytes=N` | Host-FS open + read of the staged app file | Real `rt_file_read_bytes` call on the darwin host FS |
| `HOSTED_APP_PARSE_OK path=...` | First 4 bytes are SMF magic (or ELF magic) | Real header inspection of the staged file bytes |
| `HOSTED_PROCESS_LAUNCH_OK path=...` | `rt_process_run_timeout` spawned the app as a child | Real OS-level fork/exec on darwin |
| `HOSTED_EXIT_OK exit_code=N` | Child process exited (lifecycle complete) | Real wait/reap of the child PID |
| `TEST PASSED` | All four acceptance criteria met | Terminal marker, consistent with other lanes |

### Markers NOT claimed (bare-metal only)

- `ELF_LOAD_OK` — the host dyld loader handles Mach-O segment mapping; we do not parse PT_LOAD segments
- `SMF_CLI_LAUNCH_OK` — the SMF CLI launch stack is a bare-metal runtime component not present in the hosted binary
- `SMF_WM_GUI_LAUNCH_OK` — no desktop shell on this lane
- `NATIVE_GUI_PROCESS_RENDER_OK` — no GPU/display pipeline on this lane
- `user-svc-exit:ok` — EL0 SVC round-trip is bare-metal arm64 only

## How it goes GREEN on a Mac

1. On an Apple Silicon Mac with a darwin-capable Simple compiler toolchain:
   ```
   bin/simple build --target=aarch64-apple-darwin \
     --entry=examples/09_embedded/simple_os/arch/aarch64_darwin/fs_exec_entry.spl \
     --output=build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec
   ```
2. Build also stages `build/os/darwin-aarch64/hello_world.smf` (a minimal SMF app).
3. The systest runner executes the binary; it reads the SMF, validates magic, spawns it as a child, and prints the HOSTED_* markers + `TEST PASSED`.
4. `classify_serial` finds all 5 markers in stdout → `"pass"` → GREEN.

## Why it is missing-media (RED) on Linux

- There is no darwin SDK on Linux; the binary is never built.
- The systest runner calls `run_qemu_systest` which first checks `rt_file_exists(binary_path)`.
- `build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` is absent → returns `"missing-media:..."`.
- The spec asserts `classification == SYSTEST_PASS` → **fails with missing-media**.
- This is the correct, honest behavior. `skip()` is never used.

## Build differences from bare-metal lanes

| Aspect | Bare-metal lanes | aarch64-darwin hosted |
|--------|-----------------|----------------------|
| Output format | ELF (freestanding) | Mach-O (darwin userland) |
| Linker script | Custom `.ld` | None (ld64 default) |
| Link flags | `-nostdlib -static -ffreestanding` | Standard darwin (none of those) |
| Entry | `spl_start()` | `fn main()` |
| Output channel | `serial_println()` → UART | `print` → stdout |
| Runner | `qemu-system-*` | Direct process spawn |
| File: `qemu_bios` | "default" / "none" | "" (not applicable) |
| `qemu_machine` | "virt" / "q35" / etc. | "" (not applicable) |
| `qemu_system` field | "qemu-system-aarch64" etc. | "" (not applicable; binary IS the runner) |
