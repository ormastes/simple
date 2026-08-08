# Clang/LLVM Bridge Plan (CLANG-AST + LLVM lanes)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** architecture doc Part IV (§12) and §29 Wave 5.

## Scope

Wrap and extend Clang — never fork its frontend. Components:

```text
simple-clang-export      FrontendAction/PPCallbacks/ASTConsumer → flat AST + tags/origins
simple-clang-query       QueryIR ↔ AST Matcher adapter
simple-clang-transform   MutationIR ↔ transformer/Replacements adapter
simple-llvm-pass         PassBuilder plugin, instrumentation, IR MutationIR
simple-clang-profile     remarks + PGO/sample profile → hotness tags
```

Out of scope for first release: GPU C++ preprocessor/Sema/templates (Red in
feasibility matrix); the experimental full-GPU target is constrained
preprocessed C via the parser framework, not this lane.

## Owned paths

```text
tools/clang-bridge/frontend/
tools/clang-bridge/transformer/
tools/clang-bridge/llvm_pass/
test/01_unit/tools/clang_bridge/
```

## Dependencies

- Frozen contracts: `EntityKey`/`SourceAnchor` (spelling + expansion contexts),
  QueryIR bytecode, MutationIR, `ClangAdapterCapability`.
- QUERY/MUTATE lanes for the shared engines; this lane writes adapters only.

## Phases

1. **Pin + export.** One supported Clang major; flat AST export with
   `ClangEntityIdentity` (USR/signature semantic keys for decls; anchor + kind
   + parent + ordinal for stmts/exprs; macro spelling/expansion preserved).
2. **Query.** QueryIR → AST Matcher for the supported subset; canonical-index
   evaluation otherwise. Captures return `EntityKey`, never `Decl*`/`Stmt*`.
3. **Transform.** Source-safe weaving → Replacements; control-flow-sensitive
   weaving → LLVM IR MutationIR. Explicit policy required for macro bodies,
   system headers, generated files, ambiguous template instantiations.
4. **LLVM plugin.** IR tags/origins, pass instrumentation, remarks and profile
   mapped back to source entities via MappingGraph.
5. **Modes.** C0 CPU reference → C1 hybrid (hashing, pre-index, bulk QueryIR,
   remark/profile aggregation) → C2 resident sidecars (Object VM), Clang
   remaining semantic authority and fallback.

## Acceptance

- Matcher adapter and canonical-index evaluation agree on the supported subset.
- Macro spelling/expansion location tests pass; Replacements compile cleanly.
- LLVM verifier clean after every IR mutation; remarks/debug locations
  preserved.
- Differential compile+run vs unmodified Clang on the regression subset.
- Unknown Clang major is rejected, not assumed compatible.
