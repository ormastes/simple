# Simple RISC-V SoC + Linux Boot Feature Expert

## Role

Own process knowledge for the Simple-language RISC-V cores (rv32 + rv64), their
SoC integration, the XLEN-shared logic, JTAG/AOP debug, the 4 GiB address work,
the F/D FPU, and the state of booting Linux on them (model + FPGA). Written to
stop the recurring mistake of reading ONE legacy synthesizable `.vhd` and
concluding "nothing exists."

## Read-the-history-FIRST rule (why answers went wrong 2026-07-23)

Before answering ANY architectural "does X exist / can it boot" question about
RISC-V, consult, in order: (1) the recalled `MEMORY.md` project entries
(`project_riscv_unification_*`, `project_riscv_fpga_jtag_*`, `project_riscv_fpu_*`),
(2) this wiki + the research/plan docs below, (3) the probe suite in
`scripts/check/check-riscv-hardware-gates.shs` (each probe NAMES a capability),
THEN inspect code. The failure mode was inspecting `rv32_exec_core.vhd` (a
legacy hand-written 64 KB reference core) and generalizing "rv32 has no MMU / no
big address space" — false: the CURRENT `.spl` model has Sv32 + S-mode + 4 GiB.
Distinguish three layers every time: **legacy synthesizable `.vhd` reference**
vs **current `.spl` behavioral model** vs **synthesizable-RTL generation (a
placeholder stub today)**.

## Pipeline Links

- Unification decision doc:
  `doc/01_research/hardware/riscv/riscv32_riscv64_unification_realrtl_aop_jtag_2026-07-21.md`
  (one XLEN-parameterized core 85-95% shared; AOP only for hart hooks; fail-closed
  real-RTL qualification; profiles honest — `gc`/`*d` require real F/D).
- Plan: `doc/03_plan/hardware/riscv/riscv_unification_parallel_agent_plan_2026-07-21.md`;
  JTAG: `doc/03_plan/hardware/debug/riscv_jtag_debug_plan_2026-07-21.md`.
- Linux boot guide (authoritative state + reproduction):
  `doc/07_guide/os/rv64_soc_linux_boot.md`.

## Available configurations

| Configuration | Memory path | Evidence | Command |
|---|---|---|---|
| RV32 flat | local behavioral RAM | QEMU/GHDL core | `scripts/fpga/ghdl_rv32_nvme_fw.shs` |
| RV32 BRAM SoC | core `mem_*` to synthesized BRAM banks | exact GHDL; current source-matched KV260 NVMe bundle pending | `scripts/fpga/ghdl_rv32_nvme_bram_soc.shs` |
| RV32 full AXI4 | `rv32_axi4_mem_adapter` to wait-state RAM/PS DDR | GHDL AXI4 + AXI4-Lite observation | `scripts/fpga/ghdl_rv32_nvme_axi_ram.shs` for NVMe; `scripts/fpga/ghdl_rv32_k26_ddr_boot.shs` for SimpleOS |
| RV64 full AXI4 | `rv64_axi4_mem_adapter` to wait-state RAM/PS DDR | GHDL; silicon in progress | `scripts/fpga/ghdl_rv64_k26_ddr_boot.shs` |

The RV32 NVMe `.nandram` section is ordinary linker-resident RAM. In the AXI
configuration its loads/stores traverse full AXI4; in the BRAM configuration
they do not. The AXI firmware-in-loop gate accepts host-issued Create CQ/SQ,
Identify, Write, Flush, and Read through MMIO plus queue/PRP DMA and IRQ. The
BRAM lane remains a CPU-local recovery/boot check, not host NVMe transport.

## Code Map

- **Shared XLEN layer** `src/lib/hardware/riscv_common/` — `xlen.spl`
  (`XlenConfig.rv32()/.rv64()`: mask/sign_bit/bytes_per_reg/cause_interrupt_bit),
  `alu.spl`, `decode.spl`, `rtl_decode.spl`, `csr_defs.spl`, `registers.spl`,
  `memory.spl`, `platform.spl`. BOTH cores import it; do NOT build a second common
  layer. Full single-core migration is deliberately NOT on the generic-function
  path yet (monomorphization unproven — templates must be fail-closed first).
- **rv32 core** `src/lib/hardware/rv32i_rtl/` — alu/csr/csr_s/decode/lsu/regfile/
  trap + **`mmu_sv32.spl`** (Sv32 MMU) + S-mode. 4 GiB addressing via
  `src/lib/hardware/soc_rtl/ram_sparse.spl` (sparse page-backed).
- **rv64 core** `src/lib/hardware/rv64gc_rtl/` — alu/atomics/csr/csr_s/decode/lsu/
  mmu/`mmu_sv39.spl`/mul_div/regfile/trap/**`fpu.spl`** (F/D, DI-toggle, landed
  2026-07-23, wired into `core.spl`: FP compute + load/store + fcsr CSR +
  mstatus.FS).
- **SoC** `src/lib/hardware/soc_rtl/` — `soc_top_64.spl` (bootrom→0x80000000, DRAM
  0x80000000, CLINT/PLIC/UART16550, Sv39, `soc_top_64_run` with OpenSBI
  checkpoints hit_a4/cc/fw), `ram64.spl`, `ram_sparse.spl`, `bootrom.spl`,
  `wb64_interconnect.spl`.
- **JTAG** `src/lib/hardware/debug/` (jtag_tap/riscv_dtm/dmi_bus/debug_module,
  GHDL tbs, IDCODE 0x15350067, Stages 1-3/5) + **AOP hart hooks**
  `src/lib/hardware/debug_hooks/hart_debug.spl` (repo `on pc{…} use … before`
  weave; `driver_pipeline.weave_aop` + `mir_aop_injection`). Also
  `src/lib/hardware/link_mux/` (frame/mux/jtag_route — shared-link channel mux;
  one link carries log+term+jtag). Verified 2026-07-24: `frame_probe` /
  `mux_probe` / `jtag_route_probe` ALL PASS interpreter+jit. The jtag channel
  tunnels OpenOCD `remote_bitbang`; Phase 1 reached IDCODE only — the DMI/DM
  extension (`jtag_debug_probe.spl`: halt / read-write GPR+dpc / resume against
  the rv64 core model over the muxed link) is the in-model debugger. Board
  path = BSCANE2 USER4 tunnel (`jtag_debug_chain.vhd` + `G_DEBUG_JTAG` guard,
  `openocd_kv260_bscan.cfg`, `check_kv260_jtag_debug.shs` verify/soak). THE
  debugging guide (both paths + troubleshooting):
  `doc/07_guide/hardware/fpga/simple_riscv_jtag_debugging.md`.
- **Synthesizable RTL** `examples/09_embedded/fpga_riscv/rtl/` — the real,
  SILICON-PROVEN cores (2026-07-26): `rv32_exec_core_flat.vhd` (GHDL lane),
  `rv32_exec_core_axi.vhd` + `rv32_axi4_mem_adapter.vhd` +
  `soc_top_rv32_k26_ddr.vhd` (KV260 PS-DDR4, **SimpleOS TEST PASSED on
  silicon**), `soc_top_rv32_tiny_bram.vhd`/`rv32_bram_soc.vhd` (BRAM-only,
  **TEST PASSED on silicon**, no FSBL), `rv64_exec_core_{flat,axi}.vhd` +
  `soc_top_rv64_k26_ddr.vhd` (GHDL green; silicon bring-up in progress). The
  legacy `rv32_exec_core.vhd` is the 64 KB reference/oracle. The `fpga_linux`
  bundle generator (`src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`) still
  emits `GENERATED_RTL_NOT_IMPLEMENTED` placeholders — NOT a working core.
  **Launch guide (SimpleOS + NVMe fw on the FPGA cores):**
  `doc/07_guide/hardware/fpga/simpleos_on_simple_riscv_fpga.md` §5–6 — GHDL
  rehearsal (ALWAYS also `GARBAGE_FILL=1`; sim RAM zeroes for free, real DDR is
  garbage — un-zeroed `.bss` was THE silicon killer), then bitstream
  (`build_k26_rv32_ddr_bitstream.shs` / `build_rv32_tiny_bram_bitstream.shs`),
  then `bash bringup_kv260_rv32_ddr.shs` (full psu_init BEFORE `fpga -file`,
  `.bss` zeroing with PRE/POST readback, JTAG via hw_server only).
  **Since 2026-07-26 the kernels self-zero `.bss` in `_start` (crt0)** —
  rv32 `sw`/rv64 `sd` loop over `[_sbss,_ebss)` in
  `examples/09_embedded/simple_os/arch/riscv{32,64}/boot/baremetal_stubs.c`
  (`_ebss` is `ALIGN(8)` in `common/linker_riscv_common.ld`); loader-side
  zeroing in the bringup scripts is redundant-but-kept, now ELF-derived
  (never hardcode `.bss` offsets — a relink shifts them and a stale span
  corrupts loaded `.data`), skippable via `SKIP_BSS_ZERO=1` for crt0 proof
  runs. GHDL proofs: rv32/tiny `GARBAGE_FILL=1`; rv64 `GARBAGE_FILL=1
  SKIP_BSS_ZERO=1` (its tb emulates board step 5b zeroing).

## Sanity gates (probe = capability)

- `soc_top_64_probe` → `SOC64 PROBE: ALL PASS` (interpreter only — JIT boxed-int
  61-bit defect, `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`).
- `addr4g_probe` → `ADDR4G_PROBE: ALL PASS` (4 GiB rv32 + rv64 ≥2^31).
- `check_linux_loading_rv32.shs` → `CHECK_LINUX_LOADING_RV32: PASS`.
- `check-kv260-simpleos-boot-release.shs` — REAL-BOARD release gate: fresh KV260 bring-up via `scripts/fpga/systest_kv260_bringup.shs` (outside the test runner — board runs outlive child timeouts), then the 3-tier spec `test/03_system/app/hardware/feature/kv260_simpleos_boot_silicon_spec.spl`; wired into `check-simpleos-mission-critical-release.shs` (board absent = visible SKIP).
- `check-riscv-hardware-gates.shs` — bundle (JTAG tbs + soc/core/mux/fpu probes;
  FP probes run interpreter via the `INTERP_PROBES` list).

## What is missing to boot Linux (honest)

- **rv64, `.spl` model:** Linux→/init proven on QEMU's OWN cpu with Simple's
  `soc_virt.dtb` (`build/os/rv64_soc/transcripts/qemu_ourdtb_wired.log`). On the
  Simple core, OpenSBI runs reloc→bss→fw_platform_init→C-init then **stalls
  spinning ~0x800005F4 before the banner** (open: SBI/timer or console bind).
  Full boot also needs the **JIT boxed-int fix** (interp ≈540 inst/s is too slow
  for billions of insns; JIT currently mis-executes the core).
- **rv32 product:** `core32_protected_product_entry` owns Sv32/PMP and emits
  the CPU bus; `_SocVhdlGen` owns its WB, external-DDR SoC, and K26 wrappers.
  Compiler-emitted VHDL simulation and Linux boot remain pending Stage 4.
- **rv64 product:** `core64_imac_product_entry` owns Sv39/PMP and emits the CPU
  bus; `_SocVhdlGen` owns the same PS-DDR board path. The old handwritten RV64
  synthesis entry is no longer the product path.
- **Either on FPGA:** the handwritten-RTL lane IS board-qualified for rv32 as
  of 2026-07-28 (SimpleOS `TEST PASSED` on KV260 silicon, DDR + BRAM-only; NVMe
  recovery/prevention PASS in AXI/BRAM GHDL; current source-matched KV260 USER4
  evidence is pending) — but the *Simple-emitted*
  (`_SocVhdlGen`) core path remains pending Stage 4 for both XLENs. The PL UART
  is still not host-routed; markers are read via JTAG obs regs / BSCANE2 tunnel,
  or wire a 3.3 V PMOD UART.

## Landmines

- `unit` is a RESERVED type keyword (→ "found Dot"); never a var/field name.
- Hardware `.spl` runs INTERPRETER-only (JIT boxed-int + `spl_f64_to_bits`
  miscompile). Do not "fix" bare `len(x)`→`.len()` / bare `use path.sym`→brace in
  `ram64`/`wb64`/`core.spl` to enable JIT — it exposes the broken JIT core
  (soc/boot probes FAIL). Fix the JIT codegen first.
- WC caveat: leaked jj conflict markers fail the gates at parse time; restore with
  `git checkout origin/main -- src/lib/hardware/ examples/09_embedded/fpga_riscv/`.
- Runner (2026-07-24): the deployed CLI's in-process `run` cannot resolve
  `std.hardware.*` brace-imports (bug doc
  `native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md`). Run
  hardware probes via seed delegation
  (`SIMPLE_BOOTSTRAP_DRIVER=$PWD/src/compiler_rust/target/bootstrap/simple`)
  or a scratch-named CLI copy + `simple_seed` sibling (`wjob` pattern — also
  dodges earlyoom's kill-by-name on `simple`). A Jul-23 deploy clobbered
  `bin/release/<triple>/simple` with a compile-only bootstrap binary; if
  `bin/simple` suddenly has no `run` command, restore the full CLI (backup at
  `simple.bootstrap-clobber-bak`, known-good at `build/native_probe/simple`).

## 2026-07-27 hardening campaign (gates 12/22 → 21/22)

- **Seed `@hardware` gap was the master failure**: the Rust seed's interpreter
  directive skip-list omitted `hardware`/`clocked`/`generic`/
  `flatten_struct_output` (`interpreter_eval.rs:606+`), so `@hardware` sources
  died with ``variable `hardware` not found`` — blocking 9 probes + the formal
  gate. Fixed in-seed; **takes effect only after full bootstrap redeploy**.
- **`X test <spec>` executes the spec under `bin/simple`, not X** —
  `find_simple_binary()` falls through (`cli_get_args()[0]` is the subcommand).
  Set `SIMPLE_BINARY=<binary>` for test-run evidence. Bug:
  `test_runner_child_binary_ignores_invoking_binary_2026-07-27.md`.
- rv32 generated core has **no trap machinery** (`csr_mcause`/`mepc` absent in
  all 3 lanes); C.EBREAK/illegal/AMO/unknown-op red specs live in
  `rv32_trap_completeness_spec.spl` — trap infra is the prerequisite. Flat/axi
  lanes come from `rv32_variant_sections.spl`, not `rv32_sections.spl`.
- `rv64gc_core_product*` renamed `rv64imac_core_product*` (was a false `gc`
  claim over an IMAC netlist). The `simple_rv{32,64}gc_core` family remains
  unrenamed (woven into formal gates; needs its own lane).
- Payload addresses `0x8002AB5C/6C/8C` in `rv32_exec_core.vhd` are UNREACHABLE
  dead code (`SCRATCH_BASE_WORD=16384` vs `word_index()` max 16383).
- Full ledger: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`.

## 2026-08-06 riscv64 kernel-closure campaign

- **SIMD overgeneration, not an ISLE gap** (`8053e05f683`): `vany_true.i64x2`
  was thought to be a missing ISLE lowering rule for riscv64. It was actually
  the Rust seed's hand-inlined SIMD fast path in
  `src/compiler_rust/compiler/src/codegen/instr/calls.rs` emitting Cranelift
  I64X2 ops unconditionally even on riscv64 (no `V` extension → no vector type
  exists to lower). Fixed by gating to x86_64/aarch64 with a scalar fallback
  elsewhere. Full pattern (grep for future hand-inlined SIMD intrinsics):
  `doc/00_llm_process/layer_expert/mir_lowering/skill.md` § SIMD gating.
- **`boot.spl` mangled symbol name fix** (`91644b426eb`): a hardcoded
  `boot_main` mangled symbol name was wrong; corrected.
- **`freestanding_runtime.c` volatile/barrier family** (`6890950285b`):
  `rt_volatile_read/write_u16/u32/u64`, `rt_load_barrier`, `rt_store_barrier`,
  `unsafe_addr_of` added. A later lane found two bugs in this same landing
  (`f9f85cdc443`): (1) a doc comment accidentally embedded `*/` mid-sentence,
  closing the C block comment early and cascading into ~200+ undefined-symbol
  link errors including `rt_alloc` (which was already correctly implemented);
  (2) `rt_alloc`'s bump-allocator heap limit (`g_freestanding_heap_limit =
  0x90000000`) was 128 MiB past QEMU virt's actual RAM end (`0x88000000` =
  base `0x80000000` + 128 MiB), silently approving allocations into
  non-existent memory instead of failing closed. Both fixed; the riscv64
  kernel closure now compiles and links past this file, progressing to a
  narrower ~20-symbol set (`rt_dict_new`, `rt_string_to_lower`,
  `rt_enum_discriminant`, `rt_find`, etc.) tracked as the pre-existing,
  separate dict/string/enum design gap in
  `doc/08_tracking/bug/riscv64_kernel_codegen_blocker_2026-07-20.md`.
- Also this session: `idt.spl _halt()` target-gated so the riscv64 kernel
  closure clears the C-asm stage (`1874c7a8bd8`); `runtime_legacy_core` added
  to the riscv64 sysroot C runtime build (`d0ff4e834b3`).

## RV64 SimpleOS ordered boot gate (2026-08-14)

Use `doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md` for the current
Sv39/PID1/network/SSH/WM QEMU contract. Sv39 must be read back from SATP and
PID1 must come from the process owner before network or service readiness; a
later SSH/WM marker cannot imply either prerequisite. The lane remains blocked
until a provenance-admitted Stage 4 CLI exists and every ordered receipt passes
the shared fail-closed checker.
Historical cycle 3 published Stage 2 (binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`).
Host `earlyoom` then sent Stage 3 SIGTERM at 41,394 MiB RSS on a no-swap host
with less than 10% free memory; exit 143 followed 5.4 seconds later. That parent
predates the complete `d99deb3` snapshot provider and is diagnostic only.
TODO666 is open/actionable. Its incompatible M0 draft was reverted; existing
resume-only durable sinks remain, while safe phase publication, full-bootstrap
wiring, process/RSS/signal supervision, and provenance migration are not
landed. Then a fresh current-HEAD Stage 2 and one instrumented Stage 3 run in a
fresh session; parser versus HIR retention remains unresolved. TODO667/A2
remains gated; no Stage 3/4, essential smoke, deploy, or rollback exists.
Source integration includes the IPC/VFS lifecycle wave: syscall-18
owner-checked port destruction, unique named VFS discovery, copied request/raw
reply framing, public FS binary methods, manager-owned mutation routing, and
FD READ/WRITE/SEEK/close. Resume after TODO667 with the focused SSpec and
the exact TODO806 live command. Retain `build/os/rv64-ssh-live.serial.log`, the
gate verdict, image/provenance hashes, and independent OpenSSH outcomes. Do not
turn the Stage 4 evidence blocker into another source-only completion claim.

Terra terminal-only checks of `ssh_live_entry.spl` and the WM-resource spec
returned exit 0, while the system SSpec checker load segfaulted. The newer
five-fixture compiler probe also fails its two baseline controls at build rc
139. Treat all of these as bounded diagnostics, retain the next outputs under
the canonical roots, and do not promote them to a Stage 4 or QEMU result.

P1c freezes the copied-service ABI at
`IPC_COPIED_SERVICE_TAG = 0xFFFFFFFFFFFFFFFFu64`; no port-ID/payload heuristic
may select it, and legacy zero-length sends stay legacy. Syscall 18 is
owner-only destruction. VFS close uses a monotonic issued-handle watermark for
bounded idempotent terminal knowledge; a lost reply leaves the final local FD
retryable. SOSIX I/O now shares named VFS READ/WRITE/SEEK rather than fixed
endpoint routing. After TODO667 retain one focused IPC-handoff, destroy-port, VFS-wire,
FD-route, and SOSIX-I/O log for root and the normal/highest-capability Codex
reviewer; those logs remain source-contract evidence, not a live gate result.

The current source additionally cross-checks SATP mode/root PPN against the
activated Sv39 root and keeps the SSH accept owner live after WM admission;
later accepted sessions must again prove terminal handling and accept recovery.
These changes strengthen AC-3/AC-4/AC-6 source status but are not runtime PASS.

After Stage 4 admission, boot-owner, IPC/VFS, SSH, WM, and SSpec/manual focused
rows run in parallel with disjoint log names. The combined QEMU row is serial
because it owns host port 2222 and the canonical serial/OpenSSH/QMP artifacts.
AC-8/AC-9 is accepted by H0/root static review and has no runtime dependency;
the prior reachable
WARN push is not final AC-10 evidence.
