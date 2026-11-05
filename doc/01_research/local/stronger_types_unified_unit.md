# Local Research — Stronger Types: Unified `unit`, Effects, Protocol States, LSP

**Date:** 2026-11-05
**Branch:** `work/simple-hardening-release-20261013` (base `origin/release/1.0.0`, HEAD e19cedfd911)
**Method:** read-only source audit of `D:/dev/simple-rt` (release/1.0.0 tree). All paths below are relative to that worktree. Companion design: `doc/05_design/stronger_types_unified_unit.md` (pinned-revision observations there were against an older tree; this document supersedes them for release/1.0.0 where they differ).

## 1. Declaration parsing and representation

### Self-hosted frontend (production compiler) — `src/compiler/10.frontend/`
- Tokens: `core/tokens.spl:194` `TOK_KW_NEWUNIT = 219`, `:171` `TOK_KW_NEWTYPE = 198`, keyword map `:336-337, :421-422`. **No `TOK_KW_UNIT`** — bare `unit` is not a keyword in the self-hosted frontend.
- `core/_ParserDecls/enum_module_body.spl` `parse_module_body()`:
  - `:1894` — `newunit Name: T as suffix` → lowered to a single-field struct via `decl_struct_def(...)`, then `named_type_register`, `custom_primitive_register`, `newunit_register`. Comment at `:1896-1897`: suffix-literal runtime registration is "handled by the Rust unit parser path".
  - `:1920` — `newtype Name = T` (kind 198) → same struct-wrapper lowering; auto-derives `__add__/__sub__/__mul__/__div__/__eq__/__lt__/__gt__` for numeric inner types (`:1966-2004`).
- **No distinct AST node kind** — both forms become struct decls. Nominal metadata lives in flat side tables: `core/types.spl:938-975` (`newunit_names/newunit_suffixes/newunit_underlying_type_tags`, `newunit_register/find`), serialized in the flat-pool cache at `:1839-1841`.
- Measurement catalog: `src/compiler/30.types/units/unit_registry.spl` — `struct UnitEntry` (:27), `class UnitRegistry` with `by_short/by_full/by_path/composites` dicts (:59-63), built from parser newunits as `UnitClass.Count` with 1:1 factor (:270-295). **Gap confirmed** (`unit_registry.spl:256-265`, `_ParserPrimary/asm_match_suffix.spl:343`): `unit.*` catalog declarations are "not parsed yet" and `unit_registry_lookup` has no live caller — unit-suffix typing is unfinished in the self-hosted path.
- Suffix literals: parser emits `EXPR_SUFFIXED_LIT` (`core/_AstExpr/nodes.spl:57`); HIR keeps `IntLit(value, suffix: text?)` / `FloatLit(...)` (`src/compiler/20.hir/hir_definitions.spl:598-599`). Inferencer (`src/compiler/30.types/type_infer/inference_expr.spl:551-587`) maps only primitive suffixes (i8..u64, f32); any other suffix (e.g. `km`) falls through to `case _: 64` → plain `i64`.

### Rust seed parser (bootstrap-only) — richer `unit` support
- `src/compiler_rust/lexer/identifiers.rs:241` `"unit" | "newunit" => TokenKind::Unit` (contextual); `:327` `newtype`. Dispatch `src/parser_impl/core.rs:802` (contextual: `unit = x` stays assignment).
- Forms (`src/stmt_parsing/var_decl.rs`): standalone nominal `unit UserId: i64 as uid` with multi-base union (`:971-1003`); family `unit length(base: f64): m = 1.0, ...` with optional arithmetic block (`:882-968`); compound `unit velocity = length / time` (`:846-878`, `**` exponents `:1024`). `newunit` shares the path but is rejected for compound/family forms (`:847, :883`). `newtype Name = Type` only (`:1349`).
- AST: `src/ast/nodes_units.rs` (`UnitDef`, `UnitVariant`, `UnitFamilyDef`, `UnitArithmetic`, `CompoundUnitDef`), `NewtypeDef` (`src/ast/nodes/statements.rs:453`). Tests: `src/compiler_rust/parser/tests/contextual_keyword_identifiers.rs:188`.
- Per `.claude/rules/bootstrap.md` the seed is bootstrap-only; production runs on the pure-Simple binary. **The unified-`unit` grammar must be implemented in the self-hosted frontend; seed parity matters only for bootstrap compatibility.**

### Tree-sitter / formatter / LSP
- Tree-sitter queries (`src/compiler/10.frontend/parser/treesitter/queries/*.scm`) reference `unit_declaration` (`highlights.scm:435`, `locals.scm:119`, `folds.scm:50`, `indents.scm:34`) and keyword `"unit"` (`highlights.scm:39,453`) but **not** `newunit`/`newtype`. No `grammar.js` in repo (queries only).
- No `newunit`/`newtype`/`unit` special-casing in `src/compiler/90.tools/formatter/` or LSP/MCP apps.

## 2. Type representation and layout

- Types are a plain enum, not an interner: `src/compiler/20.hir/hir_types.spl:672` `struct HirType { kind, span }`; `enum HirTypeKind` (:678) — user types are `Named(symbol: SymbolId, args: [HirType])` (:700). Nominal identity = HIR symbol id.
- Inference context: `struct HmInferContext` (`src/compiler/30.types/type_infer_types.spl:232`) with `dim_solver: DimSolver`, `trait_solver`, `current_function_effects: [Effect]`.
- **16-slot custom-primitive registry is dead code.** `src/compiler/30.types/custom_primitive_info.spl` still contains `class CustomPrimitiveRegistry` "Flat 16-slot registry" (:199), hard cap at count 16 (:252), alignment-from-size in `CustomPrimitiveInfo.create` (`alignment: r.resolve_byte_size(underlying)`, :160). Zero callers outside its own file. The live registry is the unbounded frontend arrays (`core/types.spl:921-975`).
- Layout authority (live): `src/compiler/30.types/type_layout.spl` facade → `_TypeLayout/layout_core.spl` `primitive_size` (:207), `primitive_align` (:231), `size_of_type` (:540), `align_of_type` (:545); `arch_and_verify.spl` `compute_layout` (:171).
- Dimension rules delegate to `unit_expression_equivalent` in `src/lib/common/units/model/world_units.spl:133` (`struct UnitExpression` :32, `enum UnitClass` :15). Note `dim_constraints.spl` is tensor-shape checking, unrelated.

## 3. Effect inference audit (all five design-doc gaps CONFIRMED on release/1.0.0)

`src/compiler/30.types/type_infer/inference_effects.spl` (308 lines), `src/compiler/35.semantics/effect_verifier.spl` (402 lines).

- (a) **Fail-open unknown**: `:190-192` `case _:` "conservatively assume no effects" → `[]` (comment says conservative; behavior is fail-open).
- (b) **Failed callee synthesis contributes nothing**: `:106-109` `case _: pass`.
- (c) **Unresolved method → IO-only fallback**: `:137-146` pushes `Effect(kind: IO)` — fail-closed for I/O but fabricates a complete row for other effects.
- (d) **Lambda body effects attributed at creation**: `:154-155` infers body where the lambda expression appears.
- (e) **Literals merge child effects only**: `ArrayLit/ArrayRepeat/TupleLit/DictLit` (:35-58), no own allocation effect.
- `EffectKind` enum (`hir_types.spl:908-915`): `Pure, IO, Async, Throws(HirType), Mutates, Allocates, Custom(text)`. `effects_match` ignores `Throws` payload (:268-270).
- Rows are plain `[Effect]` lists; `merge_effects` dedups via `effects_match` (:276-287); accumulation into `HmInferContext.current_function_effects` via `accumulate_effect` (:289-308), sole external call site `type_infer/inference_expr_calls.spl:32`.
- Verifier: violation kinds `EFFECT_COPY_OVER_BUDGET/IMPLICIT_COPY/UNBOUNDED_LOOP/GROWTH_IN_LOOP` (int codes, `effect_verifier.spl:45-48`), `class EffectManifest` (:126), fixpoint `effect_copy_closure` (:172) saturating at `EFFECT_COPY_CEILING`. Comments at `:371-393` admit indirect-call lower-bound and unmeasured non-struct copies.
- **No completeness tracking** (no record of which HIR kinds hit `case _:`), **no effect-summary cache**, **no LSP/MCP exposure** (grep over `src/app/mcp/**`, `src/app/simple_lsp_mcp/**` finds no effect facts).
- **Parallel unintegrated systems**: `src/compiler/35.semantics/param_effects/` (infer.spl, contracts.spl, imported_callback_receipts.spl; wired in `80.driver/driver_hir_pipeline_support.spl:50-51,403-447`) and `src/compiler/30.types/type_system/effects.spl` (2-variant `enum Effect { Sync, Async }`, Tarjan SCC propagation). Design decision needed: unify into the existing `EffectKind` row machinery rather than growing a third system.

## 4. Concurrency / TCP stdlib owners

- **Sync channel (authoritative owner)** `src/lib/nogc_sync_mut/concurrent/channel.spl`: `class Channel: _id: i64` (:123). SFFI `rt_channel_new/send<T>/try_recv<T>/recv<T>/close/is_closed` (:107). **T is generic per call**, not per channel: `send<T>` (:130), `try_send<T> -> bool` (:138), `recv<T> -> T?` (:155). **Admission status discarded**: `send()` "If channel is closed, send is silently ignored" (:126-132); only `try_send()` checks `status == 1` (:139-141). Raw-ID forge helpers exist: `channel_new_id/channel_from_id/channel_send_by_id<T>` (:191-214).
- **Async channel** `src/lib/nogc_async_mut/concurrent/channel.spl`: 9-line re-export facade of the sync owner. `green_channel.spl` is i64-only, untyped.
- **TCP sync** `src/lib/nogc_sync_mut/tcp/types.spl`: state constants `TCP_STATE_CLOSED=0..TIME_WAIT=10` as plain `pub val i64` (:6-16); errors as i64 constants (:53-59); connection is a bare 7-tuple with `tcp_connection_get/set_*` accessors (:62-151); guards `tcp_state_can_send` (:199), `tcp_state_can_receive` (:207), `tcp_state_transition_valid` (:231). **Invalid send returns `conn` unchanged (silent no-op)** (`send.spl:8-16`); **invalid receive returns `("", conn)`** (`receive.spl:8-25`).
- **Legacy `compiler_rust` duplicates**: `src/compiler_rust/lib/std/src/concurrency/channels.spl:24` (`Any`-typed SFFI, discards admission entirely); `src/compiler_rust/lib/std/src/net/tcp.spl:28,98` (async `TcpListener/TcpStream` over monoio, `Result<T, NetError>` — different model, no TCP_STATE constants).
- **No `Sender<T>`/`Receiver<T>`/typed endpoint abstraction exists** anywhere. Nearest: `class SenderId: value: i64` (`src/lib/common/types.spl:79`) — actor message-ID newtype.

## 5. Shared semantic tooling surface

- **LSP server** lives in `src/lib/nogc_sync_mut/lsp/` (not `src/app`): `main.spl:98` routes `textDocument/hover` → `lsp_handle_hover` (`lsp_handlers.spl:386`, shells out via `lsp_visibility_query_command_v1(["hover", file, line, col])`); `:131` `codeAction` → `lsp_code_action.spl` (`nested_workspace_edit` :137, `legacy_workspace_edit` :176). Advertises hoverProvider at `:120`.
- **`src/app/simple_lsp_mcp/`** is an MCP server wrapping query CLI commands (`tools.spl:49` `run_lsp_query`, `:56` `run_visibility_hover`, `:86` `run_lsp_diagnostics`; in-proc adapters `lsp_query_inproc.spl`).
- **MCP server** `src/app/mcp/`: `tool_table.spl` single tool registry (`simple_diagnostics`/`simple_symbols`/`simple_ast_query`/`simple_sem_query`/`simple_edit`/`simple_multi_edit` at :478-524).
- **CLI routing**: `src/app/cli/_CliMain/main_and_help.spl:611` (`elif first == "query"` → `cli_run_query`) → `src/app/io/_CliCommands/run_commands.spl:639` → `src/app/cli/query.spl` (dispatch :303 hover, :324 code-actions, :228 workspace-symbols, `type-at`, `sem-query`, `ast-query`). Registry: `src/app/cli/command_registry.spl:54` (`_cmd("check", ...)`). Dispatch core `src/app/cli/dispatch.spl:48`.
- **Compiler-native query API**: `src/compiler/90.tools/query_api.spl:28` `class CompilerQueryContext`, `:329` `hover_at(...) -> Option<HoverInfo>`, `:510` `rename(...) -> Option<WorkspaceEdit>`. Types: `query_types.spl:222` `struct WorkspaceEdit`; edits serialized in `fix/engine.spl:62` `fix_outcome_workspace_edit`.
- **NOT FOUND**: no unified AST/CST transaction framework (WorkspaceEdit JSON + rename only), no `inspect`/`refactor` commands, no unit-hover facts.

## 6. Build/test basics

- `bin/simple.exe` is a **Rust bootstrap seed** (v1.0.0-rc.1) that warns "bootstrap seed only". `bin/release/` does not exist; `src/compiler_rust/target/bootstrap` absent; `build/` empty. Per critical rules, the pure-Simple self-hosted binary is the default tooling; obtaining it on a fresh worktree requires `sh scripts/bootstrap/bootstrap-windows.sh` (wraps `bootstrap-from-scratch.sh`), first run needing `--full-bootstrap` (or pre-build seed via cargo) — a long build to schedule deliberately, not incidentally.
- Spec runs: `bin/simple test path/to/spec.spl` (repo-relative; absolute paths silently run nothing, `.claude/rules/testing.md:106`), `--mode=interpreter` where needed.
- Existing relevant specs: `test/01_unit/compiler/types/units_newunit_registry_spec.spl`, `test/01_unit/compiler/parser/newtype_spec.spl`, `test/01_unit/compiler/newtype_ops_spec.spl`, `test/01_unit/compiler/frontend/newunit_pool_reset_spec.spl`, `test/03_system/app/compiler/feature/world_units_newunit_spec.spl`, `test/feature/usage/unit_types_spec.spl`, `pass_unit_equivalence_spec.spl`; effects: `test/01_unit/compiler/semantics/effect_inference_spec.spl`, `effect_verifier_spec.spl`, `effect_body_facts_spec.spl`, `param_effects/param_effects_inference_spec.spl`, `test/01_unit/compiler/types/effect_scc_propagation_spec.spl`, `test/03_system/compiler/effects_core_spec.spl`, `test/feature/usage/effect_system_spec.spl`.
- `find doc/06_spec -name '*_spec.spl' | wc -l` → **0** (clean).

## 7. Key divergences from the pinned-revision design observations

| Design doc §2 claim (old tree) | Release/1.0.0 reality |
|---|---|
| `unit length(base: f64):` measurement form in production | Only in Rust seed; self-hosted frontend does not parse `unit` at all — catalog path "not parsed yet" |
| 16-slot custom-primitive registry is a live limit | Same file exists but is dead code; live registry is unbounded frontend arrays |
| `send` discards admission status | Confirmed (`send()` silently ignores closed channel) |
| Channel send/recv independently generic | Confirmed |
| Unresolved methods fall back to IO only | Confirmed |
| LSP/MCP/CLI shared tooling | Confirmed in structure; no effect/unit facts exposed yet |
