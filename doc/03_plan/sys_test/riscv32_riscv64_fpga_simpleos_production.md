# RV32/RV64 Simple-Generated FPGA CPU and Linux — System Test Plan

Status: executable acceptance written; production helpers intentionally fail
until their corresponding implementation milestones converge

Manual generation is currently blocked by the local toolchain. The current
`bin/simple` is a Rust bootstrap and cannot be used for normal tooling. An
isolated pure Stage3 compiler successfully built a current full CLI at
`build/native_probe/simple-f1n3-stage3`, but its link log contains unresolved
startup/path stubs and `spipe-docgen` exits 139. The newest isolated pure release
CLI reproduces exit 139. No manual was fabricated; the mirror must be generated
after the full-CLI startup/runtime defect is fixed.

## Primary Scenario Flow

The generated manual shall expose these exact steps:

1. `Generate RV32 and RV64 RTL from Simple sources`
2. `Exercise Sv32 and Sv39 translation plus PMP protection`
3. `Boot Linux to an interactive login on generated RTL`
4. `Run terminal login and list guest files`
5. `Program each FPGA image and capture board-origin evidence`

## Scenario Contract

| Step | Required inputs | Required observations | Fail-closed negatives |
|---|---|---|---|
| Generate RTL | pure-Simple compiler, tracked RV32/RV64 `.spl` roots | non-empty clocked/bus VHDL, source maps, hashes, changing RVFI | stub/fallback, empty architecture, constant RVFI, emitted-string/copied CPU |
| Exercise protection | memory-backed page tables and PMP regions | translated paddr, page fault, PMP deny, TLB fence for each XLEN | local constant arithmetic, uncalled production functions, tautological assertions |
| Boot Linux | pinned OpenSBI/Linux/DT/initramfs | ordered DUT-UART boot markers through `login:` | QEMU result counted as RTL, testbench-reported marker, missing artifact hash |
| Login and list | UART RX/TX, deterministic user/rootfs | accepted prompt, `ls /`, expected entries, completion marker | output-only capture, command not echoed/observed, prompt synthesized by wrapper |
| Program FPGA | board ID, bitstream, terminal transport | timing/resource/program logs plus cold/warm board transcript for RV32 and RV64 | ILA-only login claim, PS UART without proved bridge, stale bitstream/artifacts |

## Planned Executable Spec

Target:
`test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl`

Mirrored manual target:
`doc/06_spec/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.md`

Use `std.spec.*`, `step("...")`, and built-in matchers only. Missing setup or
checker helpers must call `fail(...)` or `assert(false)`. Hardware-unavailable
rows remain visible as `blocked` and cannot be `skip()` or PASS.

## Environment and execution order

1. Pure-Simple self-hosted compiler and focused VHDL/GHDL tools.
2. Production Sv32/Sv39/PMP unit and integration fixtures.
3. ACT4 plus strict RVFI/SymbiYosys proof tools.
4. Pinned OpenSBI/Linux/DT/rootfs and QEMU media oracle.
5. Generated-RTL Linux simulator with bidirectional UART driver.
6. Vivado/KV260/JTAG, Linux-sized DDR path, and proved bidirectional terminal.

Run each converged gate once per session. At most three fix/verify cycles are
allowed per milestone. A missing external tool or board is `blocked`; a
semantic mismatch is `fail`.

## Traceability IDs

- ST-RV-001: compiler-generated RV32 and RV64 CPU/SoC RTL provenance.
- ST-RV-002: Sv32/Sv39 translated fetch/load/store and page-fault behavior.
- ST-RV-003: PMP allow/deny/lock behavior after translation.
- ST-RV-004: OpenSBI/Linux/init/login on generated RTL for both XLENs.
- ST-RV-005: interactive UART login plus `ls /` for both XLENs.
- ST-RV-006: ACT4 and real RVFI/SBY evidence for both declared profiles.
- ST-RV-007: KV260 timing/resource/program/cold/warm evidence for RV32.
- ST-RV-008: equivalent independent KV260 evidence for RV64.
- ST-RV-009: generated operator manual quality and stale-doc audit.

## REQ traceability matrix

| Requirement | Executable cases | Evidence | Coverage state |
|---|---|---|---|
| REQ-001 | primary; reject noncanonical RTL; reject incomplete provenance | compiler/VHDL/source-map/hash logs | designed; helper pending |
| REQ-002 | primary; reject noncanonical RTL; reject bypass/cross-arch; reject vacuous formal | RV32 ACT4/RVFI/GHDL | designed; helper pending |
| REQ-003 | primary; reject bypass/cross-arch; reject vacuous formal | Sv32/PMP unit, integration, formal | designed; helper pending |
| REQ-004 | primary; reject noncanonical RTL; reject bypass/cross-arch; reject vacuous formal | RV64 ACT4/RVFI/GHDL | designed; helper pending |
| REQ-005 | primary; reject bypass/cross-arch; reject vacuous formal | Sv39/PMP unit, integration, formal | designed; helper pending |
| REQ-006 | primary; reject QEMU/output-only; reject stale physical evidence | SoC/DT/UART/DDR logs | designed; helper pending |
| REQ-007 | primary; reject QEMU/output-only; reject stale physical evidence; reject provenance | media/QEMU/RTL manifests and transcripts | designed; helper pending |
| REQ-008 | primary; reject noncanonical RTL; reject vacuous formal; reject provenance | ACT4/RVFI/SBY logs | designed; helper pending |
| REQ-009 | primary; reject bypass/cross-arch; reject QEMU/output-only; reject stale physical | KV260 reports and transcripts | designed; helper pending |
| REQ-010 | primary; reject noncanonical RTL; reject incomplete provenance | SPipe manual, guide, review audit | designed; helper pending |

Every REQ maps to at least three executable cases. The primary scenario and all
negative cases intentionally remain red until their named production checkers
replace the explicit `fail(...)` helpers.

## NFR verification matrix

| NFR | Mechanism |
|---|---|
| NFR-001 | two clean deterministic generation runs and full SHA-256 manifest |
| NFR-002 | positive/negative contract fixtures, focused coverage, ACT4, strict formal |
| NFR-003 | parsed Vivado DRC/timing/utilization/power reports tied to bitstream |
| NFR-004 | bounded cold/warm RTL and board login/`ls` transcripts |
| NFR-005 | clean-work-directory rebuild and manifest comparison |
| NFR-006 | page/PMP matrices plus no-bus-on-fault formal property |
| NFR-007 | independent board/JTAG/terminal evidence per XLEN |
| NFR-008 | docgen zero-stub/freshness/layout audit and primary review record |

## Manual rendering and capture policy

- The primary scenario is visible and uses the five frozen operator steps.
- Negative/provenance/formal matrices are `@manual: folded`.
- Execution, log, protocol, binary, and artifact evidence is linked rather than
  embedded.
- Raw test code remains folded below the manual flow.
- No hardware-unavailable acceptance is skipped.

## Current toolchain evidence

- Stage3 full-CLI build: `1358 compiled, 0 cached, 0 failed`.
- Built artifact SHA-256:
  `201c54d288764ab9be9649e4f39ce0ce732ea6bd9868703f6e47646fdef385f3`.
- Build log: `build/native_probe/riscv_f1_n3_stage3_build.log`.
- Docgen attempts: two distinct pure full CLIs, both exit 139 before output.
- GDB identifies `rt_process_run_inherit` argument corruption; the self-exec
  in-process route avoids the crash but times out after 120 seconds with no
  output. The three-cycle cap is reached for this session.
- The focused test and diagram renderer remain unexecuted because they share
  the same known-broken full-CLI startup path; repeating the crash is not
  acceptance evidence.
- Open blocker:
  `doc/08_tracking/bug/pure_simple_full_cli_process_run_inherit_spipe_docgen_crash_2026-07-18.md`.
