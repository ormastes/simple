# Current source-owner contracts

STATUS: PASS for the bounded bootstrap source-contract correction.

The executable owners are five existing specifications: backend LLVM adapter
trace, backend LLVM object-path lifetime, backend MIR text signature, lint query
AST projection, and lint query closure index. This test-only change preserves
negative assertions and direct grammar, and corrects their actual owner scope
or intended literal bytes.

- LLVM adapter: source placeholders are escaped literal text. Direct/compiled
  operation boundaries are validated. The retained target configuration wins,
  and each operation samples its environment fallback exactly once.
- LLVM lifetime: the negative callee-return predicate remains asserted within
  validated compile_ir_to_object_path boundaries. An unrelated sibling function
  legitimately contains the old text conversion; the actual consuming owner
  already freezes the target triple inline.
- MIR signature: the current LLVM normal/bootstrap calls and direct SSA driver
  call preserve the originating function span. Additional negatives prohibit
  omitted spans at the actual LLVM call owners; old spanless negatives remain.
- Query AST: warning placeholders remain literal. The outer owner splits source
  once; validated AST projection boundaries prohibit another split.
- Query closure: the existing behavioral diagnostic remains required. Source
  assertions recognize group-qualified assigned keys and the dictionary lookup;
  candidate scanning and obsolete helper negatives remain unchanged.

Stage1 Windows producer SHA256:
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Host windows/AMD64, target x86_64-pc-windows-msvc. Zero rebuilds.

The original one-pass66-example receipt remains historical evidence. Targeted
checks select only eight previously failing examples: adapter3, lifetime1,
closure1, ASTprojection2, MIRsignature1. All eight passed. The MIR signature
needed two changed fix/check cycles; other checks needed one. Six unchanged
passing examples from these five specs were not replayed: MIR behavior2 and
AST projection4. Coverage is incremental14criteria, not a full-suite rerun.
A distinct literal-byte control passed1/1. No skipped/dropped examples.

Evidence: build/phase1-negated-matcher-20261011/residual-results.json,
residual-span-cycle2.log, literal-identity.log, and residual-evidence.json.
All eight source owners are unchanged between the diagnostic base dbca09fd567
and landing base2a11aeb0009. Whitespace validation passes; misplaced executable
specs0. Parent exact-diff review found noP0/P1 findings.

Pure-Simple runtime and native product behavior remain unqualified. This scope
corrects tests and documents bootstrap observations; production source is
unchanged. Direct grammar and the ten genuine product-contract failures remain
OPEN in PR3015: coverage4, MIRtrace2, perfdiagnostics3, rawSFFIsnapshot1.