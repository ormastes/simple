# RISC-V FPGA Linux NFRs

Historical NFR interpretation for the completed helper-proof milestone:

- NFR-RFL-001: Preparation must fail fast with explicit diagnostics for missing board, lane, or Linux artifact inputs.
- NFR-RFL-002: Generated project manifests must be deterministic for review and CI comparison.
- NFR-RFL-003: Hardware boot checks must be gated behind an exact board profile; generic profiles are prepare-only.
- NFR-RFL-004: The historical slice must not regress existing VHDL backend and targeted RISC-V hardware/compiler/QEMU tests while RV64-first pipeline work advances elsewhere.
- NFR-RFL-005: Generated hardware helper source, VHDL source-map headers, and RTL manifests must remain deterministic and reviewable across identical inputs.
- NFR-RFL-006: Decode and immediate helper lowering must stay slice-based and overlay-driven for the implemented helper set; fallback shift/mask reconstruction in the generated helper path is not acceptable.
- NFR-RFL-007: Top-level handwritten shell control must dispatch through generated helper contracts and must not regress into raw opcode `case` selection for bounded supported instruction classes.

Canonical active NFRs for Linux-platform truth now live in `doc/02_requirements/nfr/rv64_linux_rtl_pipeline.md`.
