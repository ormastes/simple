<!-- codex-design -->
# Bootstrap compiler/backend stage split requirements

**Selected direction (2026-08-15):** after one admitted success of the current
bootstrap pipeline, migrate to four explicit artifact stages:

1. Rust builds the bootstrap Simple seed.
2. The seed builds the pure-Simple compiler with Cranelift as default.
3. Stage 2 builds the pure-Simple compiler with LLVM as default.
4. Stage 3 builds tooling only and links it against a versioned Stage-3
   compiler artifact; compiler sources are not rebuilt.

- **REQ-BSPLIT-001:** Each stage records source, producer, backend, target,
  compiler/runtime ABI, artifact, command, and content hashes.
- **REQ-BSPLIT-002:** Stage 2 defaults to Cranelift.
- **REQ-BSPLIT-003:** Stage 3 defaults to LLVM.
- **REQ-BSPLIT-004:** Stage 4 compiles only tool-owned modules and records zero
  compiler-source compile units.
- **REQ-BSPLIT-005:** Stage 4 links a versioned compiler archive/interface;
  textual names, timestamps, and stale cache hits are not authority.
- **REQ-BSPLIT-006:** The existing pipeline remains canonical until it records
  one admitted end-to-end success.
- **REQ-BSPLIT-007:** A clean full rebuild remains an audit/equivalence command,
  not the normal Stage-4 path.
