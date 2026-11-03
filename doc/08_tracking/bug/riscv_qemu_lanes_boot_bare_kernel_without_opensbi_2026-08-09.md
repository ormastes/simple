# RISC-V QEMU scenario lanes boot bare `-kernel` with no OpenSBI firmware proxy

- **Filed:** 2026-08-09 (stream J2, comment-cheat spec repair)
- **Status:** OPEN — spec left RED deliberately
- **Severity:** high — violates `.claude/rules/board-runnable.md`; the RISC-V
  acceptance lanes cannot produce a board-runnable artifact.

## Rule violated

`.claude/rules/board-runnable.md`:

> **Real-firmware proxy, always:** boot via OVMF pflash (x86_64), OpenSBI
> (riscv), or EDK2/AAVMF (aarch64) — **never** QEMU `-kernel` pass semantics.
> The proxy exists so the same artifact runs on hardware.

## Defect

`_build_scenario_command_impl` — `src/os/_QemuRunner/scenario_exec.spl:417-464` —
builds every scenario command line and **never pushes `-bios`**. Its only
firmware-aware branch is the `x64-desktop-uefi` special case, which skips
`-kernel` in favour of OVMF pflash supplied through `scenario.qemu_extra`. Every
other non-ARM scenario falls into the `else` arm:

```
    else:
        args.push("-kernel")
        args.push(kernel_path)
```

So `riscv64-virtio-fat32-smf`, `riscv32-virtio-fat32-smf`, `riscv64-hosted` and
`rv64-x25519-probe` are launched as `qemu-system-riscv{32,64} ... -kernel <elf>`
with no OpenSBI. That is exactly the banned pass semantics: QEMU synthesises the
M-mode environment the ELF expects, and no physical board will reproduce it.

### The `-bios` support exists, but on the wrong builder

`build_qemu_command` / `build_qemu_command_with_options` in
`src/os/_QemuRunner/os_build_run.spl:807-868` **do** handle firmware:

```
    # BIOS/firmware (OpenSBI uses "default", empty means no -bios flag)
    if target.qemu_bios == "default":
        args.push("-bios")
    elif target.qemu_bios != "":
        args.push("-bios")
        args.push(target.qemu_bios)
```

Two things defeat it:

1. The **scenario** lane (`build_scenario_command`) is a separate builder that
   never consults `target.qemu_bios` at all.
2. All 17 literal target definitions in
   `src/os/_QemuRunner/runner_targets.spl` set `qemu_bios: ""`, i.e. *no* `-bios`
   flag, including the RISC-V ones. The only "opensbi" string in that file is
   `_loader_name_for_arch` (line 225-230), which is a **report label** used for
   provenance text — it does not reach any QEMU argument.

Net: nothing in the repo ever puts OpenSBI on a RISC-V QEMU command line.

## How this stayed invisible

`test/01_unit/os/qemu_runner_spec.spl` and its duplicate
`test/unit/os/qemu_runner_spec.spl` asserted the *banned* contract:

```
expect(cmd64).to_contain("-kernel")
```

A spec pinning `-kernel` can only ever ratify the violation. The x86_64 UEFI
lane in the same file does the opposite and asserts
`expect(cmd.contains("-kernel")).to_equal(false)` plus the OVMF pflash operand —
so the correct pattern was already present one screen away, just never applied
to RISC-V.

## Repro

```
bin/simple test test/01_unit/os/qemu_runner_spec.spl
```

Fails in `it "builds QEMU commands with RISC-V kernels and VirtIO block disks"`
on the newly added `expect(cmd64).to_contain("-bios")`.

Observed 2026-08-09 with `src/compiler_rust/target/bootstrap/simple`
(33,653,056 bytes, mtime Aug 9 23:10) — the runner prints the whole command
line it built, which is the direct evidence:

```
expected [qemu-system-riscv64, -machine, virt, -cpu, rv64, -m, 512M,
          -serial, stdio, -display, none, -no-reboot,
          -kernel, build/os/simpleos_riscv64_smf_fs.elf,
          -global, virtio-mmio.force-legacy=false,
          -drive, file=build/os/fat32-riscv64.img,if=none,id=rvdisk,format=raw,
          -device, virtio-blk-device,drive=rvdisk] to contain -bios
```

No `-bios` anywhere: the ELF is handed straight to QEMU via `-kernel`.

`SPEC FILE VERDICT: test/01_unit/os/qemu_runner_spec.spl ... executed=33
passed=19 failed=14`. Thirteen of those failures pre-date this change (stale ARM
scenario lookups, x86_64 FAT32 media drift, frontend-contract text drift); the
RISC-V `-bios` failure is the one added here.

## Unblock condition

Teach `_build_scenario_command_impl` the firmware proxy:

- give RISC-V scenario targets `qemu_bios: "default"` (QEMU ships OpenSBI as its
  default RISC-V BIOS) or an explicit `fw_dynamic.bin` path;
- have the scenario builder emit `-bios` from that field before `-kernel`, the
  same way `build_qemu_command` already does;
- keep `-kernel` — under OpenSBI it is the standard S-mode payload handoff, not
  pass semantics.

Then flip these specs green and add the matching board bring-up transcript
required by the board-evidence bar.

## Related, not fixed here

- `rv64-x25519-probe` and `riscv64-hosted` take the same `else` arm and have the
  same gap.
- The x86_32 lane (`build_qemu_command(get_target(Architecture.X86))`,
  asserted at `test/01_unit/os/qemu_runner_spec.spl:262`) also boots bare
  `-kernel` with `qemu_bios: ""`, where the rule wants OVMF pflash. Same family,
  separate fix.
- `.claude/rules/board-runnable.md` already records the aarch64 EFI-stub gap.

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: RISC-V QEMU/OpenSBI board-runnable rule violation, needs a QEMU boot to verify; spec is deliberately left RED per the record itself. No change made.

## Scoped repair and corrected diagnosis — 2026-11-03

Reviewed source: `009546cbe28c082986078e505bdee9152b559689`.
The historical inference that omitting `-bios` means no OpenSBI is incorrect
for current QEMU `virt`. [QEMU's RISC-V documentation](https://www.qemu.org/docs/master/system/target-riscv.html)
documents automatic default OpenSBI loading. Bounded probes using QEMU 11.1.1
confirmed that both RV64 and RV32 print OpenSBI v1.8.1 and an S-mode handoff
with either omitted BIOS or `-bios default`; `-bios none` prints no firmware
banner. These probes ran without a kernel for three seconds each. They prove
firmware selection semantics, not SimpleOS or board acceptance.

There is still a concrete projection defect: `_scenario_from_target` drops
`OsTarget.qemu_bios`. For example, a custom firmware path or explicit `none`
in that field is ignored unless duplicated in `qemu_extra`. The scoped repair
appends a default-empty `QemuScenario.qemu_bios` field, carries it through target
and catalog-lane projections, and reconciles it with legacy extra arguments.
The command builder emits one firmware pair before the kernel payload, keeps
matching duplicate selections singular, and returns an empty command on
conflicting selections or malformed operands. Both production launch callers
already reject empty commands before starting QEMU.

Focused regression:
`test/01_unit/os/qemu_firmware_projection_v1_spec.spl` exercises the real target
projection and command builders for default, none, custom, omitted,
duplicate, conflicting, malformed, and current RISC-V lane selections.
**Simple spec execution remains UNRUN**: no admitted general Simple test
runtime was available in this scoped session. Source review and native
firmware-only probes must not be reported as a passing Simple spec run.

The RV32 catalog currently labels its lanes `OpenSbi` while explicitly
selecting `-bios none`; its linker places the M-mode kernel at `0x80000000`.
This repair preserves that boot choice. Switching to OpenSBI requires a
separate boot ABI/layout migration or an honest metadata correction; flipping
the flag alone is unsafe. Full bug closure still needs the matching kernel
and board evidence. The historic report and its evidence remain above.

Probe artifacts retained at
`/tmp/parallel-three-tracks-20261103/bugs/riscv-opensbi/`: `probe.sdn` records
both QEMU executable hashes, exact argument variants, timeout exits, and
scope; the six `rv32-*`/`rv64-*` logs preserve the observations.
