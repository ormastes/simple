# NFR Requirements: RV64 Linux RTL Pipeline

Date: 2026-04-24
Status: Draft

NFR-RV64-LINUX-RTL-001
Architecture truth shall live in shared hardware/common and backend target capsules, not in duplicated orchestration strings.

NFR-RV64-LINUX-RTL-002
Existing RV64 hardware tests and RISC-V backend tests shall remain non-regressed.

NFR-RV64-LINUX-RTL-003
Compiler-facing RISC-V Linux target policy shall be deterministic and inspectable from tests without requiring external tool invocation.

NFR-RV64-LINUX-RTL-004
`hardware.fpga_linux` default output shall remain deterministic and file-based so synthesis and follow-on validation wrappers can consume it without reparsing free-form text.
