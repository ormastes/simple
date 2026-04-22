# RISC-V FPGA Linux NFRs

- NFR-RFL-001: Preparation must fail fast with explicit diagnostics for missing board, lane, or Linux artifact inputs.
- NFR-RFL-002: Generated project manifests must be deterministic for review and CI comparison.
- NFR-RFL-003: Hardware boot checks must be gated behind an exact board profile; generic profiles are prepare-only.
- NFR-RFL-004: The feature must not regress existing VHDL backend, RV32 RTL simulation, or RISC-V QEMU boot tests.
