# Cross-Compile Matrix Plan (target x output kind x host)

Status: active, 2026-10-27. Owner: cross-compile matrix lane.
Specs: `test/02_integration/compiler/cross/*_cross_spec.spl` (helpers in
`cross_matrix_helpers.spl`). Bugs: `doc/08_tracking/bug/bug_xc_*_2026-10-27.md`.

## Rules
- Toolchain: clang + lld only. Windows targets: llvm-mingw UCRT
  (`aarch64/i686/x86_64-w64-mingw32`). No MSVC, no GCC.
- CPU levels use LLVM names: `x86-64`, `x86-64-v2`, `x86-64-v3`, `x86-64-v4`
  (shared with the SIMD tier lane). Pass the level explicitly; the default
  x86_64 CPU is `x86-64-v3`.
- Every row stays visible. A row that cannot run is UNSUPPORTED (by design,
  with the reason) or BLOCKED (missing runner or host, with owner and resume
  command). Never `skip()`, never a vacuous PASS.
- Run paths use real firmware (OpenSBI on QEMU `virt`); never `-kernel`
  pass-through or `isa-debug-exit` (.claude/rules/board-runnable.md).

## How each row is checked
| kind | build | check |
|------|-------|-------|
| exe | `native-build hello.spl --target T -o out` | readobj format + machine; entry point (PE `AddressOfEntryPoint` / ELF `Entry`); run output `xc-ok` where runnable |
| obj | `--emit-object` on `lib.spl` | readobj format + machine; `llvm-nm` defines `xc_add` |
| static lib | `--emit-archive` | member format + machine; `llvm-nm` defines `xc_add` |
| dylib | `--emit-shared` | format + machine; `xc_add` in the PE export table / ELF dynamic symbols |

Run paths: aarch64 Windows uses an ARM64 Windows host or `qemu-aarch64`, else
PE machine and imports only. i686 Windows runs under WoW64 on the x86_64
Windows host; i686 Linux uses `qemu-i386` user mode. riscv bare metal uses
`qemu-system-riscv{64,32} -M virt` + OpenSBI, else ELF header and arch checks.
riscv SimpleOS boots SimpleOS through OpenSBI with
`scripts/qemu/simple-qemu-settings.shs` + `simple-qemu-host-admission.shs`
and runs the exe from the guest FS. x86-64-v4 runs only on an AVX-512 host
(cpuid `avx512f`); otherwise check that the CPU level reached LLVM by
instruction selection (`a << b` lowers to BMI2 `shlx` at v3/v4 and to `shlq`
at baseline) and scan for zmm/EVEX.

## Evidence (host = Windows 11 x86_64, 2026-10-27)
Binary: `C:/dev/p3new/stage2.exe` (phase-3 stage2), copied to
`C:/dev/xc/simple_xc.exe`, run with `C:/msys64/clang64/bin` first on PATH,
from the repo root. Host CPU: Xeon E5-2673 v4 (Broadwell, **no AVX-512**).
No QEMU on this host; WSL fails to start (`E_FAIL`), so every QEMU run row is
BLOCKED here.

| target | exe | obj | static lib | dylib | run |
|--------|-----|-----|-----------|-------|-----|
| aarch64-pc-windows-gnu | FAIL: BUG-XC-CROSS-EXE-LINK | PASS: COFF-ARM64, 0xAA64, xc_add | PASS: COFF-ARM64 members, xc_add | FAIL: BUG-XC-SHARED-LINK-DFLAG | BLOCKED: no exe; no qemu-aarch64 or ARM64 host |
| riscv64-unknown-none-elf | FAIL: BUG-XC-CROSS-EXE-LINK | PASS: elf64-littleriscv, EM_RISCV | PASS | UNSUPPORTED by design (no dynamic loader on bare metal); the rejection diagnostic is wrong, see BUG-XC-BAREMETAL-SHARED-DIAG | BLOCKED: no qemu-system-riscv64 |
| riscv32-unknown-none-elf | FAIL: BUG-XC-RV32-GCC | PASS: elf32-littleriscv, EM_RISCV | PASS | UNSUPPORTED by design; the diagnostic is wrong, see BUG-XC-BAREMETAL-SHARED-DIAG | BLOCKED: no qemu-system-riscv32 |
| i686-pc-windows-gnu | FAIL: BUG-XC-CROSS-EXE-LINK | PASS: COFF-i386, 0x14C | PASS | FAIL: BUG-XC-SHARED-LINK-DFLAG | WoW64 available; blocked on the exe |
| i686-unknown-linux-gnu | FAIL: BUG-XC-CROSS-EXE-LINK | FAIL: emits COFF-i386, not ELF (BUG-XC-ELF-ON-WIN) | FAIL: same | FAIL: BUG-XC-SHARED-LINK-DFLAG | BLOCKED: no qemu-i386 |
| x86_64-pc-windows-gnu @ x86-64-v4 | FAIL: BUG-XC-HOST-GNU-LINK | PASS via `SIMPLE_NATIVE_CPU`: `shlx` emitted; `--cpu=` ignored (BUG-XC-CPU-FLAG-IGNORED) | PASS: xc_add | FAIL: BUG-XC-SHARED-LINK-DFLAG | BLOCKED: host lacks AVX-512 |
| riscv64-unknown-simpleos | FAIL: BUG-XC-CROSS-EXE-LINK | PASS: elf64-littleriscv | PASS | FAIL: BUG-XC-SHARED-LINK-DFLAG (supported in principle: kernel DlOpen/DlSym) | BLOCKED: no qemu-system-riscv64 |
| riscv32-unknown-simpleos | FAIL: BUG-XC-RV32-GCC | PASS: elf32-littleriscv | PASS | FAIL: BUG-XC-SHARED-LINK-DFLAG | BLOCKED: no qemu-system-riscv32 |

Summary: objects and static archives cross-compile for every target (except
the i686-linux format bug). No cross executable and no dylib links yet.

## Host dimension
Each target row above is to be reproduced from every host. Only Windows was
reachable from this lane.

| host | status | owner | resume command |
|------|--------|-------|----------------|
| Windows x86_64 | MEASURED (table above) | cross-compile lane | `SIMPLE_XC_BIN=<stage2> bin/simple test test/02_integration/compiler/cross/` |
| Linux x86_64 | BLOCKED: WSL `E_FAIL` on this host; needs a Linux box or a working WSL | cross-compile lane / infra | on Linux: `SIMPLE_XC_BIN=bin/simple bin/simple test test/02_integration/compiler/cross/` |
| Linux riscv64 (guest) | BLOCKED: needs Linux + QEMU | linux-riscv64 bootstrap lane | `sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --provision` then run the specs in the guest |
| macOS | BLOCKED: no macOS host in this lane | macOS bootstrap owner | on macOS: same `bin/simple test` command |
| FreeBSD | BLOCKED: QEMU wrapper requires a Linux host with QEMU | FreeBSD bootstrap lane | `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`, then run the specs in the VM |
| SimpleOS | BLOCKED: no self-hosted `native-build` in the SimpleOS guest yet, and no QEMU here | SimpleOS toolchain lane | boot via OpenSBI using `scripts/qemu/simple-qemu-settings.shs`; run the specs once an in-guest compiler exists (doc/03_plan/os/in_guest_clang_selfhost_board_plan.md) |

## Board path
riscv bare metal and SimpleOS rows are developed against QEMU `virt` +
OpenSBI so the same ELF boots on a physical RISC-V board through its OpenSBI
/ U-Boot chain (doc/03_plan/os/simpleos/hw_qemu/). Board evidence (board
identity, boot path, serial transcript) is not yet collected: blocked on the
exe rows (BUG-XC-CROSS-EXE-LINK, BUG-XC-RV32-GCC).

## Next
1. BUG-XC-SHARED-LINK-DFLAG: the one-line linker fix is in PR (see the lane report), and target-based dispatch follows.
2. BUG-XC-CROSS-EXE-LINK: `clang --target=` plan plus per-triple runtime.
3. BUG-XC-CPU-FLAG-IGNORED: coordinate with the SIMD tier lane (`--cpu-tier`).
4. Re-run the specs on the next stage2. Install QEMU (or repair WSL) to unblock the run rows.
