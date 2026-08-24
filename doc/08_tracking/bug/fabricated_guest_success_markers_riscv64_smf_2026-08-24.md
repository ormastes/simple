# Fabricated guest success markers: five `rt_riscv_*` probes were `return 1;` (2026-08-24)

## Summary

Five `rt_riscv_*` probes in
`examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c:24-41`
had **no implementation**. Each body was exactly `return 1;` — an
unconditional SUCCESS. Every caller therefore printed its ok-shaped marker on
every boot, whether or not the capability existed:

| symbol | markers it made unconditionally true |
|---|---|
| `rt_riscv_nvfs_probe` | `[riscv-nvfs] image read ok` |
| `rt_riscv_smf_cli_probe` | `FS_MOUNT_OK`, `SMF_DISCOVERY_OK` |
| `rt_riscv_smf_cli_load` | `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK` |
| `rt_riscv_smf_gui_probe` | `SMF_WM_GUI_LAUNCH_OK` |
| `rt_riscv_native_gui_process_render` | `NATIVE_GUI_PROCESS_RENDER_OK` |

These are exactly the five rows baselined at
`config/simpleos_fabricated_rt_baseline.sdn:219-223` for
`simpleos_riscv64_smf_fs.elf`.

## Census (the systemic question)

The task framing was that these were **auto-stubbed**. They are not. The
riscv64 link path deliberately links no `auto_stubs.c`
(`src/compiler/70.backend/backend/simpleos_native_linkers.spl:325`), and the
Rust hosted stub generator emits `return 0;`
(`src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:346`), which
takes the caller's FAILURE branch and cannot launder a transcript. The
fabrication was **hand-written C**.

A tree-wide scan of every `*.c` under `examples/09_embedded/simple_os` and
`src/os/kernel/arch` for an `rt_*` function whose entire body is `return 1;`
finds **exactly these five, in this one file, and nothing else**. The
population of success-emitting fabricated stubs is therefore bounded at 5, not
55: the other 50 baselined symbols are all in
`simpleos_wm_production_desktop.elf` and are infrastructure
(`rt_string_builder_*`, `rt_dma_*`, `rt_font_glyph_*`, ...) with no ok-shaped
marker attached.

## Untrustworthy prior evidence

Any transcript from `simpleos_riscv64_smf_fs.elf` citing the markers above is
void. Consumers that grade on them, and whose prior passes must be re-earned:

- `scripts/qemu/check_simpleos_riscv_telnet_serial.shs` (greps `TEST PASSED`)
- `test/03_system/os/qemu/os/appscan/riscv_smf_appscan_qemu_spec.spl:66-72`
- The §27 row of 2026-08-24 in the hardening plan, which cited
  `FS_MOUNT_OK` -> `SMF_DISCOVERY_OK` -> `ELF_LOAD_OK` -> `SMF_CLI_LAUNCH_OK`
  as a real transcript. `FS_MOUNT_OK` there is FAT32-adjacent, not nvfs.

Both consumers grade on the **transcript**, not the exit code, so they will now
honestly go RED. That is the intended outcome, not a regression.

## Fix

The stubs are NOT deleted — `simpleos_riscv64_smf_fs.elf` needs the symbols to
link and the entries reference them via `extern fn`. Each now calls
`rt_riscv_stub_announce`, which writes `STUBBED <name>` to the serial console
via the non-static `rt_riscv_uart_put`
(`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:1510`, reachable
because the file `#include`s that runtime), and returns **0**. A transcript can
never again read as evidence of a capability that was never written.

## Second defect found: failure paths that exit SUCCESS

33 sites across 8 guest entry files print `TEST FAILED` and then call
`rt_qemu_exit_success()` within 3 lines. Any lane grading on the guest exit
code reads that as a pass. Both current consumers grade on the transcript, so
this is a **latent** hazard rather than a currently-firing one — but it is
precisely the mechanism an `isa-debug-exit`-graded lane would trust.

9 riscv64 sites are fixed in this commit
(`shared_service_smoke_entry.spl` x6, `simple_tool_probe_entry.spl` x2,
`hosted_entry.spl` x1), each gaining the `extern fn rt_qemu_exit_failure()`
declaration in the exact form `smoke_entry.spl:3` already uses.

**24 remain blocked**, frozen shrink-only in
`scripts/check/fabricated_success_exit_baseline.txt`. The blocker is exact:
`rt_qemu_exit_failure` is defined in exactly ONE place tree-wide,
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:95`.
arm32, arm64 and riscv32 have no definition, so flipping their call sites would
break the link or silently auto-stub the symbol — a worse fabrication than the
one being fixed. Implementing it for those three arches is the prerequisite.

## Gate

`scripts/check/check-no-fabricated-success-markers.shs` — fail-closed, verdict
as last stdout line, 0 files scanned is ERROR not PASS, `--selftest` fatal
(6 fixtures). No existing gate could see either defect: the fabricated-rt
baseline ratchet classifies by objdump body shape at LINK time and had all five
BASELINED as accepted debt; `-fsyntax-only` compiles `return 1;` happily; and
the `rt_*` symbol-set guard only counts definitions.

Evidence, each rc read directly into a variable on the line after the
invocation, never through a pipe:

```
sh scripts/check/check-no-fabricated-success-markers.shs --selftest
  PASS — 6 selftest fixture(s) checked, 0 failures            SELFTEST_RC=0

sh scripts/check/check-no-fabricated-success-markers.shs
  PASS — 403 file(s) scanned, 0 fabricated-success site(s)
  (0 unconditional-success rt_* stubs; 24 failure-exits-success site(s)
   frozen in scripts/check/fabricated_success_exit_baseline.txt, 0 new,
   0 stale)                                                   SCAN_RC=0

# real-tree incident replay: restore `return 1;` on rt_riscv_nvfs_probe
  FAIL — 403 file(s) scanned, unconditional-success-stub:
  ./examples/09_embedded/simple_os/arch/riscv64/boot/
  full_networking_runtime.c:58                                REPLAY_RC=1
# restored
                                                              RESTORED_RC=0

clang --target=riscv64-unknown-none-elf -march=rv64gc -mabi=lp64d
  -ffreestanding -fno-pic -nostdinc -fsyntax-only
  examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c
                                                              CLANG_RC=0
```

## Still open (not addressed here)

- **`isa-debug-exit` in `scripts/os/run_x86_64_fs_exec_ovmf.shs:74`** — real
  and confirmed, on a lane whose own name claims OVMF compliance
  (`:70-71` do use OVMF pflash correctly). Removing the device turns the
  guest's port-0xf4 write into a no-op, so the guest runs to timeout and the
  runner must own termination: the replacement is a serial transcript teed to a
  file plus a timeout loop grading on markers, and the runner's exit status
  must come from that grep, not from QEMU. Not attempted here rather than done
  half-way. `/usr/bin/grep -rn 'isa-debug-exit'` finds it in 37 files overall;
  most are x86 guest-side port writes, which are harmless once no lane grades
  on them.
- **`-kernel` at `src/os/qemu_systest_contract.spl:140` (riscv64)** — boots
  `build/os/simpleos_riscv64_smf_fs.elf`, i.e. exactly the ELF whose transcript
  this record proves was fabricated. Migrating that lane to OpenSBI real
  firmware is moot until it has honest evidence to migrate; sequence the
  capability implementation first.
- **`-kernel` at `src/os/qemu_systest_contract.spl:227` (arm64)** — the
  kernel-side half is done (`crt0.S` Image header + self-relocation, gated by
  `check-simpleos-arm64-unified-boot-contract.shs`). The contract edit itself
  still needs a rebuilt `simpleos_arm64_fs_exec.elf` on the EFI chain, and
  there is no self-hosted `bin/simple` (Stage 3 SEGVs), so it stays blocked for
  the reason already filed in
  `arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`.

## Retraction filed against this record (2026-08-24, filesystem lane)

The §27 row of 2026-08-24 titled "SimpleOS's own filesystems: FAT32 / dbfs /
nvfs across the QEMU lanes" (commit `038f1278541`) claimed, as its FAT32
verdict, **"mounts and reads, real transcript"** on the strength of a riscv64
boot showing `FS_MOUNT_OK` -> `SMF_DISCOVERY_OK` -> `ELF_LOAD_OK` ->
`SMF_CLI_LAUNCH_OK`.

**That verdict is withdrawn.** Every one of those four markers is on the
fabricated list above: `FS_MOUNT_OK` and `SMF_DISCOVERY_OK` came from
`rt_riscv_smf_cli_probe`, `ELF_LOAD_OK` and `SMF_CLI_LAUNCH_OK` from
`rt_riscv_smf_cli_load`, both of which were `return 1;`. The boot was real and
rc=0, but it demonstrated nothing about FAT32: no mount was proven and no ELF
was proven loaded. The `FS_LS_*` directory listing in the same transcript is not
covered by the five fabricated probes and may be real, but it was not
independently verified and is not being claimed here.

FAT32's honest status is therefore **unproven in QEMU**, alongside dbfs and
nvfs — not "working". Nothing in that commit's code changes depended on the
claim; the retraction is to the evidence row only.
