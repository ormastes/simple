# Compiler-owned source-to-LLVM IR NFRs

<!-- codex-design -->

- **NFR-LLVMIR-001:** The compiler API must not import `src/app/**`.
- **NFR-LLVMIR-002:** The app facade is not re-exported by broad app or I/O
  packages; only compile commands that need it retain the compiler closure.
- **NFR-LLVMIR-003:** Module names and IR texts are accumulated in pre-sized
  parallel arrays. No quadratic whole-bundle concatenation or MIR dictionary
  merge is permitted.
- **NFR-LLVMIR-004:** Target validation performs no tool lookup or host probe for
  an explicit non-host triple.
- **NFR-LLVMIR-005:** Existing bootstrap-only shortcuts cannot manufacture
  empty MIR or trivial IR on this API.

