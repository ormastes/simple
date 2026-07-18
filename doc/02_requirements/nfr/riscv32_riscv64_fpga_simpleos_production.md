<!-- codex-research -->
# RV32/RV64 Simple-Generated FPGA CPU and Linux — Non-Functional Requirements

Status: **Selected — N3 physical FPGA language qualification**

Selection date: 2026-07-18. The user selected **N3**, which includes generated-
core correctness and dual-architecture Linux RTL qualification. Every target
applies independently to RV32 and RV64.

## NFR-001 — Determinism and provenance

- Identical tracked inputs and compiler/tool versions shall produce byte-
  identical generated RTL and reproducible software/bitstream manifests.
- Evidence shall record SHA-256 hashes for Simple sources, compiler binary,
  generated RTL, firmware, kernel, DT, rootfs, bitstream, and transcript.
- Generated files shall carry source-map/provenance metadata and shall not be
  accepted from an untracked cache or fallback lane.

Verification: two clean generation runs compare hashes; the evidence checker
rejects any missing/mismatched provenance field.

## NFR-002 — Fail-closed correctness

- Unsupported hardware constructs, missing tools/artifacts, empty entities,
  constant RVFI, absent assertions, unavailable boards, timeouts, and terminal
  mismatches shall report `fail` or `blocked`, never `pass`.
- No unconditional PASS testbench, marker-only executor, identity MMU bypass,
  or QEMU/external-CPU substitution may enter production evidence.
- Focused tests target at least 80% branch coverage for new MMU/PMP/compiler
  integration logic; architectural/formal suites provide system-level evidence.

Verification: positive and negative contract fixtures plus focused Simple unit,
integration, ACT4, RVFI, and SymbiYosys gates.

## NFR-003 — FPGA implementation quality

- Vivado implementation shall report zero DRC errors, no inferred latches or
  combinational loops in the product CPU/SoC, and non-negative worst timing
  slack at the declared board clock.
- Utilization, Fmax, BRAM/URAM, DSP, LUT, FF, and power estimates shall be
  retained for both lanes.
- Frequency and resource ceilings shall be frozen in this document after the
  first complete real RV32 and RV64 implementations; invented pre-synthesis
  limits are prohibited.

Verification: parsed synthesis, implementation, timing, DRC, utilization, and
power reports tied to the programmed bitstream hash.

## NFR-004 — Boot and terminal reliability

- Each architecture shall complete one cold boot and one warm-reset boot on
  generated RTL simulation and on KV260.
- Each run shall reach `login:`, accept input, reach a shell, execute `ls /`,
  and observe the expected root entries without manual transcript editing.
- Every automated runner shall have an explicit timeout. Measured generated-RTL
  and board boot ceilings shall be frozen after the first successful baseline.

Verification: timestamped bidirectional transcripts with command/response
boundaries and DUT/board provenance.

## NFR-005 — Reproducible operation

- A clean documented host shall be able to rebuild media, generated RTL, formal
  harnesses, and bitstreams using pinned versions or recorded immutable tool
  identities.
- Production wrappers shall execute cached compiled artifacts, avoid repeated
  full-tree scans/retries in hot paths, and preserve exact commands and logs.
- Generated-RTL and physical-board evidence shall remain separate from QEMU and
  external-oracle evidence in all reports.

Verification: clean-work-directory reproduction and manifest comparison.

## NFR-006 — Isolation and protection

- Sv32/Sv39 permissions, privilege transitions, page faults, access faults, and
  PMP shall prevent unauthorized fetch/read/write before a bus side effect.
- PMP locked entries and M/S/U transitions shall follow the pinned RISC-V
  privileged specification. Fault cause, address, and privilege evidence shall
  be precise enough to diagnose a failed access.

Verification: positive/negative page-table and PMP matrices in unit,
integration, architectural, and bounded formal tests.

## NFR-007 — Hardware evidence integrity

- Board evidence shall name the connected KV260 serial/JTAG identity, Xilinx
  part, programming tool, bitstream hash, clock/reset source, DDR path, and
  bidirectional terminal path.
- FPGA completion requires board-origin output and accepted input; GHDL, QEMU,
  ILA-only markers, or zero-byte UART captures remain supporting/blocker
  evidence only.
- One architecture cannot reuse the other architecture's bitstream,
  transcript, or done mark.

Verification: fail-closed preflight plus independent RV32/RV64 programming,
cold-boot, warm-reset, login, and `ls` evidence rows.

## NFR-008 — Documentation and review quality

- Requirements, architecture, design, system test, generated manual, guide,
  implementation, and reports shall use the same feature slug and retain
  REQ/NFR traceability.
- Lower-model sidecar findings are advisory until the primary normal/highest-
  capability reviewer verifies them against source and accepts exclusions,
  coverage claims, manual quality, and final done marks.
- No executable `.spl` spec may exist under `doc/06_spec`.

Verification: documentation freshness/traceability audit, sidecar review log,
SPipe docgen with zero stubs, and the production-readiness verifier.
