# Per-context frontend parse state (`ParseContext`)

Status: plan (item 32). Prerequisite named in
`incremental_build/build_runner_fiber_scheduler_v1.md` §8.1.

## Problem

The frontend parse path keeps its state in module-scope `var`s: 761 of them
across 75 files under `src/compiler/10.frontend` (measured 2026-10-25 at
`origin/release/1.0.0` `108f16883a0`, `grep -rn '^var \|^pub var '`). Two
parses in one process therefore cannot overlap: fibers would clobber each
other's pools, and threads would race. Today parallel parse means child
processes (`--parse-fibers=i/n`).

Main owners (line numbers approximate):

| file | state |
|------|-------|
| `core/types.spl` | flat AST pools `span_pool_*`, `tok_pool_*`, `sym_*`, `scope_starts`, `named_type_*`, `newunit_*`, `custom_primitive_*`, `fn_sig_*`, `generic_param_*`, composite tables; cleared by `reset_all_pools` |
| `core/lexer.spl` | `lex_state`, cursor slots, `lex_all_*` |
| `core/parser.spl` | `par_*` (errors, warnings, imports, fixed-array side channel, slots, generation) |
| `core/_Ast/module_state.spl` | lexer-state slots through persistent-owner state |
| `core/_AstExpr/nodes.spl`, `_Ast/decl_nodes.spl`, `ast_stmt.spl`, `_ParserDecls/enum_module_body.spl` | AST node arenas |
| `_FlatAstBridge/module_assembly.spl` | `_fab_capture_*` arm/record/take |
| `frontend_parse_cache.spl` | scope memo, hit/miss/store counters (process-wide by intent: stay global) |

## Constraint

Simple has no thread-local module variables, and many globals are `pub var`
read directly by other files (`parser_decls_*`, `flat_pool_codec`,
`lexer`, `c_codegen`, the test runner). A big-bang rewrite to explicit
`ctx` parameters touches hundreds of call sites in the self-hosting
compiler and cannot be verified without a bootstrap. So the move is staged,
each stage behavior-preserving and separately landable.

## Stages

1. **Snapshot/install (fiber interleaving).** Per owner file, add a plain
   struct holding exactly that file's parse globals plus
   `<owner>_state_take() -> S` (moves current globals into `S`, installs
   fresh empty ones) and `<owner>_state_install(s: S)`. A top-level
   `ParseContext` aggregates them (`parse_context_take/install`). The
   current globals remain the *active* context, so all existing code is
   unchanged. A cooperative fiber scheduler swaps contexts at park/resume,
   which makes in-process fibers safe (not yet parallel). Order:
   `types.spl` pools, lexer, parser, module_state, AST arenas, bridge capture.
   Each landing ships a spec that parses file A, takes, parses B, installs A
   and checks A's pools are intact.
2. **Accessor indirection.** Replace direct cross-file reads of `pub var`
   pools with accessor functions in the owner file, one owner per PR, so the
   storage location becomes private to its owner.
3. **Context-owned storage.** Once every owner is private, move each owner's
   storage into a field of one active `ParseContext` held in a single
   global slot. Swap cost drops from O(#globals) to one pointer.
4. **True parallelism.** Needs either (a) a language/runtime thread-local
   slot for the active-context pointer (feature request to file), or (b)
   threading `ctx` through the parser entry points. Decide after stage 3,
   when the only global left is the one slot.

### Stage 1 status (2026-10-25)

Landed per-owner snapshots: `FlatPoolState` (#4505), `LexerState` (#4512),
`ParserState` (#4513), `AstLexerSlotState` (#4514), `StmtStoreState`
(#4515), `PendingDeclAttrState` (#4516), `ExprStoreState` (#4518),
`DeclStoreState` (#4519), `FabCaptureState` (#4521), combined by
`src/compiler/10.frontend/parse_context.spl`. Still outside the snapshot:

- process env channels: `SIMPLE_PARSER_HAD_ERROR` and the `parser_env_i64`
  line/col mirror in parser.spl, plus the expr/stmt/decl env-mirror
  high-water slots. They need a per-context home before fibers interleave
  parses that hit error paths.
- `module_decl_slots` in `_Ast/decl_nodes.spl` (multi-line initializer).
- the ~600 remaining module vars in other frontend files; audit each as
  per-parse (add an owner snapshot) or process-wide (leave).
- arena generation/hardening (`ast_gen_*`, `ast_reset_seq`,
  `ast_harden_*`) stays process-wide by design.

Process-wide caches/counters (`frontend_parse_cache.spl`) stay global but
must become atomic or per-worker before stage 4.

## Verification

Stages 1-3 are pure refactors: existing frontend specs under
`test/01_unit/compiler/frontend/` must stay green on the deployed binary, and
the new take/install spec must pass. No stage changes parse output.
