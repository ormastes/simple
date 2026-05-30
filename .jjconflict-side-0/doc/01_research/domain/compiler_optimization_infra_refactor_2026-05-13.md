<!-- codex-research -->
# Compiler Optimization Infrastructure Refactor - Domain Research

Date: 2026-05-13

## Sources

- LLVM New Pass Manager: https://llvm.org/docs/NewPassManager.html
- LLVM new pass plugin guide: https://llvm.org/docs/WritingAnLLVMNewPMPass.html
- MLIR Pattern Rewriter: https://mlir.llvm.org/docs/PatternRewriter/
- LLVM ORC v2 dynamic library/JIT design: https://llvm.org/docs/ORCv2.html

## Summary

LLVM's new pass manager documentation recommends using `PassBuilder` and
default optimization pipelines such as `buildPerModuleDefaultPipeline(O2)` as
the normal production path. It also warns that analysis access across IR levels
can create quadratic compile-time behavior, so passes should be grouped by IR
unit and reuse cached analyses where possible.

LLVM supports dynamically loaded new-pass-manager plugins, but those are best
for optional extension points, research, instrumentation, or out-of-tree
experiments. Correctness-critical lowering, stable diagnostics, target ABI
cleanup, and hot-path semantic rewrites should remain built into the compiler
or statically linked into release tools.

MLIR's pattern rewriter model supports a useful shape for Simple's pattern
layer: explicit rule registration, static benefit/cost, root filtering, debug
labels, and bounded greedy application to a fixed point. Simple's first
practical step is not a full MLIR-style engine; it is to make rule providers
explicit and keep hot lookup allocation-free.

## Recommendation For Simple

- Keep Simple semantic optimizations in MIR before LLVM.
- Use LLVM default pipelines for LLVM IR.
- Keep hot optimizer rules built in for release binaries.
- Add dynamic loading only behind a versioned provider interface, disabled from
  hot paths unless a rule set is explicitly enabled.
- Prefer indexed/direct lookup by callee or root operation over scanning or
  rebuilding rule tables during instruction walks.
