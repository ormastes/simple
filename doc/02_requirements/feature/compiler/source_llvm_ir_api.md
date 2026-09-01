# Compiler-owned source-to-LLVM IR requirements

<!-- codex-design -->

- **REQ-LLVMIR-001:** The public operation accepts a source path, an explicit
  LLVM target triple, and an explicit bare-metal policy.
- **REQ-LLVMIR-002:** Success is produced only after real source loading,
  parsing, HIR lowering/type checking, monomorphization, MIR lowering and LLVM
  translation.
- **REQ-LLVMIR-003:** The result preserves each compiled module as an
  independent LLVM IR unit; it never concatenates complete LLVM modules.
- **REQ-LLVMIR-004:** The target triple used by MIR policy and emitted LLVM
  headers is derived from the call argument, not ambient target environment.
- **REQ-LLVMIR-005:** Empty/unknown triples, hosted/bare-metal policy mismatch,
  missing source, phase failures, missing MIR units, and empty IR fail closed.
- **REQ-LLVMIR-006:** Simple app callers use one thin selectively imported CLI
  facade. `app.io` owns no compiler stub, export, or raw extern.
- **REQ-LLVMIR-007:** CLI object/link modes compile every returned IR unit;
  single-file emit modes refuse a multi-unit result rather than silently
  dropping dependencies.
- **REQ-LLVMIR-008:** Once no Simple caller references the raw ABI, all obsolete
  Rust interpreter/runtime/codegen/linker registrations are removed atomically.
- **REQ-LLVMIR-009:** Contract coverage compares distinct source programs and
  proves their generated modules differ and contain their own source-dependent
  symbols; a target-only trivial module cannot satisfy the contract.

