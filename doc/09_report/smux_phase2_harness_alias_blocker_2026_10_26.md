# Smux Phase2 canonical-harness alias blocker — 2026-10-26

**H0 FAILED; H1/H2/M1–M3 NOT_RUN.** The first actual driver frontend returned
native exit 1, child-exit, cleanup not needed. Root reports peak tree RSS
3,284,216 KiB under the enforced 5,859,375 KiB limit: this was not OOM.
No executable was linked; no framework or feature case ran. The current
small-module inventory remains **46 authored / 0 executed**.

## Retained evidence and independent causes

Artifacts: `build/review/phase2-smux-framework-driver-1/compile.log`,
`compile.receipt`, and `smux_framework_driver.exe.go-to-end.sdn`.
Manifest SHA-256:
`de04428888985048c3bb3f5b85da44cc980d121b6a0133d22e12a16e745959c8`.
Producer remains immutable Phase2 `13d73267…8b270b`.

All 96 HIR modules succeeded. MIR lowered 112 logical modules: 87 succeeded,
25 failed; the manifest records 211 diagnostics, zero objects, link skipped.
The compiler itself truncated middle stderr; classification uses the retained
complete failure manifest rather than treating that omitted text as clean.

| Diagnostic class | Count | Evidence |
|---|---:|---|
| Ambiguous imported extern provider owner | 91 | First/second providers have identical physical snapshot paths under `compiler.frontend.core.*` and `compiler.core.*` aliases |
| Duplicate imported-global declaration | 120 | Four token `TOK_DEDENT`/`TOK_EOF` rows; 116 AST expression-constant rows from the same duplicated providers |

These are two diagnostics for one alias/provider-identity failure family.
No additional independent driver-signature, wrapper, file-I/O, syntax or
allocation failure appears in this manifest. This does not certify later stages.

## Why a driver spelling change is insufficient

`source_facts.spl:74` imports `compiler.frontend.core.lexer`.
`lexer.spl:19–21` imports `compiler.core.tokens`, `lexer_chars`, `lexer_types`;
line 24 imports `compiler.frontend.core.lexer_struct`; line 28 imports
`compiler.core.ast`. `ast.spl:18–19` re-exports frontend `_Ast` modules;
`_AstExpr/nodes.spl:2` imports frontend `ast_expr`, while `_Ast/module_state.spl:24`
imports `compiler.core.ast_expr`. Mixed aliases therefore persist below any
one-line driver import change. No such patch or retry is justified by this evidence.

## Existing source repair and limits

Current pure-Simple source has `_driver_unique_physical_sources` for parsing.
More specifically, `driver_mir_provider_aliases.spl:92` checks canonical owner,
same physical path, admitted source identity and extern contract before
coalescing providers. `driver_pipeline_lowering.spl:818/857` applies that
selection; `driver_mir_physical_owners.spl:87` explicitly covers bootstrap
shortcuts. This is a relevant repair already in source, **not evidence that
immutable Phase2 contains or executes it**. Compiler ownership and admitted
producer refresh belong to the compiler lane; this review changes neither.

The old integrated tree's `source-readiness.sdn` records materialized aliases,
`compiler_launched:false`, and `budget_status:UNKNOWN_EXCEPTION_NOT_GRANTED`.
Its incremental repin reuses materialization receipts. Those receipts and
receipt-owned alias dirt are not successful framework-build admission; repeating
normalization in another directory would not establish a new solution.

Retain prior runner failures, unknown cumulative harness history, the separate
H0 BOM setup failure, and this actual H0 frontend failure. No cycle ledger is
reset; no cache-generator-cap exception is granted. This diagnosis ran no build,
retry, generator or executable and changed no driver/compiler/import source.
