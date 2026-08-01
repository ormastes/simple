# aarch64-darwin Contract Snippet — Orchestrator Merge Guide

This document contains the **exact code** to be inserted into two shared files
by the orchestrator after all parallel agents have committed their own changes.

**DO NOT edit `src/os/qemu_systest_contract.spl` or
`src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` directly** — two other
agents own those files during this parallel work session. This snippet is
copy-paste ready for the orchestrator's merge step.

---

## 1. Insert into `src/os/qemu_systest_contract.spl`

Add the following six functions **after the last existing arch descriptor block**
(currently after `x86_32_timeout_ms()`), before the `Run helper` section.

Find the insertion anchor — the line that reads:
```
pub fn x86_32_timeout_ms() -> i64:
    60000
```

Insert immediately after the `60000` line (and its blank line separator):

```spl
# ---------------------------------------------------------------------------
# aarch64-apple-darwin hosted descriptor (native macOS process — NOT QEMU)
#
# This lane runs the built darwin binary directly as a child process.
# There is no QEMU, no bare-metal boot, no UART serial. Output is captured
# from stdout. The binary path serves as both kernel_path (missing-media check)
# and qemu_bin (the executable to run). qemu_args is [] — the binary reads
# its app path from a hardcoded constant in fs_exec_entry.spl.
#
# On Linux: binary is absent → run_qemu_systest returns missing-media → RED (expected).
# On Apple Silicon Mac: binary present → process runs → markers in stdout → GREEN.
# ---------------------------------------------------------------------------

pub fn aarch64_darwin_binary_path() -> text:
    "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec"

pub fn aarch64_darwin_app_path() -> text:
    "build/os/darwin-aarch64/hello_world.smf"

pub fn aarch64_darwin_qemu_bin() -> text:
    # Not QEMU — this IS the binary to execute directly as a host process.
    "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec"

pub fn aarch64_darwin_qemu_args() -> [text]:
    # No extra args — the binary reads app path from a hardcoded constant.
    []

pub fn aarch64_darwin_markers() -> [text]:
    # Hosted marker set — asserts REAL host-process capabilities only.
    # Bare-metal-only markers (ELF_LOAD_OK, user-svc-exit:ok, SMF_WM_GUI_LAUNCH_OK,
    # NATIVE_GUI_PROCESS_RENDER_OK) are intentionally absent — they would be lies.
    ["HOSTED_FS_READ_OK",
     "HOSTED_APP_PARSE_OK",
     "HOSTED_PROCESS_LAUNCH_OK",
     "HOSTED_EXIT_OK",
     "TEST PASSED"]

pub fn aarch64_darwin_timeout_ms() -> i64:
    15000
```

### How the spec uses these

The spec (`test/03_system/os/qemu/sys_qemu_aarch64_darwin_fs_exec_spec.spl`) calls:
```spl
run_qemu_systest(
    "aarch64-darwin",
    aarch64_darwin_binary_path(),   # kernel_path — missing-media check
    aarch64_darwin_app_path(),      # image_path  — second missing-media check
    aarch64_darwin_qemu_bin(),      # qemu_bin    — the binary to execute
    aarch64_darwin_qemu_args(),     # qemu_args   — [] (no extra args)
    aarch64_darwin_markers(),       # markers     — HOSTED_* marker set
    aarch64_darwin_timeout_ms()     # timeout_ms  — 15s
)
```

`run_qemu_systest` is a generic process-runner. On Linux both files are absent →
`missing-media:build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` is returned
immediately. On a Mac both are present → the binary runs → classify_serial checks
stdout for all 5 markers → returns `"pass"`.

---

## 2. Insert into `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`

In `simpleos_platform_targets()`, the list currently ends with the riscv32 target
followed by a closing `]`. Add the aarch64-darwin target as the **7th element**
(append before the closing `]`, after the riscv32 closing `)`).

Find the insertion anchor — the last lines of the function:
```
            notes: "32-bit RISC-V virt-machine lane"
        )
    ]
```

Replace with:
```
            notes: "32-bit RISC-V virt-machine lane"
        ),
        SimpleOsPlatformBuildTarget(
            name: "aarch64-apple-darwin",
            aliases: ["aarch64-darwin", "apple-silicon", "m1", "m2", "m3"],
            arch: Architecture.Arm64,
            arch_name: "aarch64",
            bits: 64,
            isa: "aarch64",
            abi: "aapcs64",
            float_abi: "hard",
            native_target: "aarch64-apple-darwin",
            clang_target: "aarch64-apple-darwin",
            qemu_system: "",
            qemu_machine: "",
            qemu_cpu: "",
            qemu_serial_kind: "",
            qemu_serial_base: 0u64,
            boot_firmware_contract: SimpleOsFirmwareContractKind.HostedPayload,
            default_image_layout: SimpleOsImageLayoutKind.HostedVirtioFat32,
            board_adapter_id: "",
            linker_script: "",
            default_entry: "examples/09_embedded/simple_os/arch/aarch64_darwin/fs_exec_entry.spl",
            output: "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec",
            platform_slug: "aarch64-darwin",
            kernel_output: "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec",
            disk_image_output: "build/os/darwin-aarch64/hello_world.smf",
            staged_toolchain_apps: [],
            qemu_smoke_lane: _lane_contract(
                "aarch64-darwin-smoke",
                SimpleOsLaneKind.HostedCompileSmoke,
                SimpleOsFirmwareContractKind.HostedPayload,
                SimpleOsImageLayoutKind.HostedVirtioFat32,
                "examples/09_embedded/simple_os/arch/aarch64_darwin/fs_exec_entry.spl",
                "",
                "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec",
                "",
                "",
                [],
                15000,
                [],
                [],
                "",
                "build/os/darwin-aarch64/hello_world.smf"
            ),
            qemu_acceptance_lane: _lane_contract(
                "aarch64-darwin-fs-exec",
                SimpleOsLaneKind.HostedCompileSmoke,
                SimpleOsFirmwareContractKind.HostedPayload,
                SimpleOsImageLayoutKind.HostedVirtioFat32,
                "examples/09_embedded/simple_os/arch/aarch64_darwin/fs_exec_entry.spl",
                "",
                "build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec",
                "",
                "",
                [],
                15000,
                [],
                ["HOSTED_FS_READ_OK",
                 "HOSTED_APP_PARSE_OK",
                 "HOSTED_PROCESS_LAUNCH_OK",
                 "HOSTED_EXIT_OK",
                 "TEST PASSED"],
                "",
                "build/os/darwin-aarch64/hello_world.smf"
            ),
            qemu_additional_lanes: [],
            board_lane: nil,
            source_roots: ["examples"],
            boot_c_sources: [],
            boot_asm_sources: [],
            grandfathered_native_sources: [],
            boot_impl_kind: SimpleOsNativeImplementationKind.Simple,
            runtime_impl_kind: SimpleOsNativeImplementationKind.Simple,
            standalone_asm_policy: SimpleOsStandaloneAsmPolicy.Disallowed,
            c_flags: [],
            asm_flags: [],
            link_flags: [],
            notes: "aarch64-apple-darwin hosted lane — native Mac process, no QEMU, no bare-metal. Goes GREEN on Apple Silicon Mac, RED (missing-media) on Linux by design."
        )
    ]
```

### Enum variant rationale

| Field | Chosen variant | Rationale |
|-------|---------------|-----------|
| `boot_firmware_contract` | `HostedPayload` | No firmware; hosted process. Exact enum variant exists (part1 line 28). |
| `default_image_layout` | `HostedVirtioFat32` | Closest existing variant for "hosted app image" — no native-only variant exists. |
| `boot_impl_kind` | `Simple` | The entry is a `.spl` file compiled by the Simple toolchain. |
| `runtime_impl_kind` | `Simple` | Pure Simple, no embedded ASM. |
| `standalone_asm_policy` | `Disallowed` | No ASM in the darwin hosted entry. |
| `lane_kind` (both lanes) | `HostedCompileSmoke` | Closest existing variant; there is no `NativeProcessExec` variant. Adding one requires editing part1 (out of scope). |

### Notes on blank/zero fields

- `qemu_system`, `qemu_machine`, `qemu_cpu`, `qemu_serial_kind`: `""` — not applicable; no QEMU
- `qemu_serial_base`: `0u64` — not applicable
- `linker_script`: `""` — ld64 handles darwin binaries; no GNU linker script
- `c_flags`, `asm_flags`, `link_flags`: `[]` — darwin toolchain defaults; build system fills in when cross-compiling on Mac
- `board_adapter_id`: `""` — no board
- `staged_toolchain_apps`: `[]` — no toolchain staging for the hosted lane

### _lane_contract positional arg order (15 args)

For reference, the exact parameter order of `_lane_contract` (from part1 line 249):
```
name, lane_kind, firmware_contract, image_layout, entry, linker_script,
output, qemu_memory, qemu_bios, qemu_extra, timeout_ms,
staged_apps, extra_markers, board_adapter_id, media_path_hint
```

All 15 positional args are used in both lane contracts above.

---

## Verification checklist (post-merge)

After the orchestrator merges both snippets:

- [ ] `bin/simple check src/os/qemu_systest_contract.spl` — no errors
- [ ] `bin/simple check src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` — no errors
- [ ] `bin/simple test test/03_system/os/qemu/sys_qemu_aarch64_darwin_fs_exec_spec.spl` — RED with `missing-media:build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` (expected on Linux)
- [ ] The missing-media classification contains the binary path, not a nil/crash

The spec is **intentionally RED on Linux** — that is the correct honest result.
