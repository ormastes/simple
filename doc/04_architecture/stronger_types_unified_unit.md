# Architecture — Stronger Types: Unified `unit`, Effects, Protocol States, LSP

**Date:** 2026-11-05
**Branch:** `work/simple-hardening-release-20261013` (base `origin/release/1.0.0`)
**Requirements:** `doc/02_requirements/feature/stronger_types_unified_unit.md` · **Design:** `doc/05_design/stronger_types_unified_unit.md` · **Research:** `doc/01_research/local|domain/stronger_types_unified_unit.md`

## 1. Position and strategy

Extend the existing self-hosted compiler pipeline and stdlib owners; add no parallel type/effect/edit systems. The Rust seed (`src/compiler_rust`) receives only compatibility lowering for legacy spellings needed during bootstrap — it is never the production surface.

Phasing (mirrors design §11.1, re-cut against release/1.0.0 reality):

- **P1 — Canonical unit metadata (frontend)**: one declaration parse path for all `unit` roles in `src/compiler/10.frontend`, lowering into the existing single-field-struct representation plus an extended side-table record. Legacy `newunit`/`newtype` branches delegate to the same lowering.
- **P2 — Parser/tooling surface**: keyword deprecation diagnostic + fix; formatter/tree-sitter query updates; query-API unit hover.
- **P3 — Effect hardening**: fail-closed unknown handling and completeness tracking in `inference_effects.spl`; summary publication via existing cache/query layers.
- **P4 — Typed endpoints**: payload-bound channel endpoints and observable admission in `src/lib/nogc_sync_mut/concurrent/`; TCP typestate wrappers in `src/lib/nogc_sync_mut/tcp/`.
- **P5 — Protocol descriptors**: optional finite session continuation types (stdlib library layer only, no new grammar).
- **P6 — Analysis modes + LSP/CLI/MCP**: `invest` build mode gating; `simple inspect`/`simple refactor` commands; MCP tool entries; LSP hover additions — all routed through one compiler-native query API.
- **P7 — Migration/retirement**: package migration with previewed edit plans; version-gated keyword retirement.

## 2. Component architecture

```
10.frontend                          30.types / 35.semantics
┌─────────────────────────┐          ┌──────────────────────────────┐
│ parse_module_body        │          │ units/unit_registry (live)   │
│  ├─ unit decl (NEW) ─────┼──┐       │ type_infer/inference_effects │
│  ├─ newunit (legacy) ────┼──┤       │  └─ unknown/completeness     │
│  └─ newtype (legacy) ────┼──┤  ┌──▶ │ effect_verifier              │
│ canonical_unit_lower ────┼──┘  │    │ param_effects (integrate)    │
│ side tables (extended) ──┼─────┘    └──────────────────────────────┘
└─────────────────────────┘          90.tools/query_api ──▶ LSP/CLI/MCP
                                                             (one semantic service)
src/lib/nogc_sync_mut                                        ┌────────────────┐
 ├─ concurrent/channel.spl  ──▶ Channel<T> endpoints ───────▶│ simple_lsp_mcp │
 ├─ concurrent/sender_receiver (NEW)                        │ mcp/tool_table │
 └─ tcp/*                   ──▶ TcpStream<R,W> typestate ──▶│ cli query.spl │
src/lib/... session.spl (NEW, P5)                            └────────────────┘
```

### 2.1 Canonical unit representation (P1)

- **Parse**: new branch in `parse_module_body()` (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`) keyed on a new `TOK_KW_UNIT` token (contextual, mirroring the seed's approach: `unit` remains a valid identifier in expression position — follow `asm_match_suffix.spl` and existing contextual keyword handling). Disambiguation after `unit Name`: `(` + `base:` → measurement family/derived; `=` → alias; `:` → nominal (with optional `as suffix` and optional invariant body); otherwise → zero-payload marker (lowered to existing unit/enum-marker representation).
- **Lower**: all roles produce the existing `decl_struct_def` single-field-struct shape (reuse `named_type_register`, `custom_primitive_register`), so type checking, layout (`_TypeLayout/`), and codegen are untouched. Role metadata goes to an extended record beside the current flat arrays in `core/types.spl:938-975`: `unit_role` (nominal | alias | measurement_family | marker), optional predicate ref, optional suffix, optional dimension expression ref. Alias role records `Named(target)` identity directly (no new nominal symbol), preserving alias semantics for overload/trait/equality.
- **Measurement**: normalize dimension expressions into `unit_registry.spl` entries with real `UnitClass`/`UnitExpression` data (replacing today's 1:1 Count placeholders and dead lookup path), consuming the new family declarations. Suffix literal typing (`inference_expr.spl:551-587`) resolves non-primitive suffixes against the registry instead of falling through to `i64`.
- **Registry scale**: keep the unbounded frontend arrays as the live store; the dead 16-slot `CustomPrimitiveRegistry` in `custom_primitive_info.spl` is removed or reduced to its actually-used `PrimitiveTypeResolver`/`PrimitiveAbiNames` helpers (decision at impl time; removal preferred per REQ-UNIT-06).

### 2.2 Effect hardening (P3)

- `inference_effects.spl`: `case _:` at `:190-192` returns `[Effect(kind: Custom("unknown"), ...)]` (or a new `EffectKind.Unknown`) instead of `[]`; failed callee synthesis (`:106-109`) and unresolved methods (`:137-146`) mark the row incomplete via a completeness flag on the accumulation context rather than fabricating completeness. IO-only fallback is retained as a *partial* fact, never a complete row.
- `EffectsMatch`: `Throws` payload comparison tightened to payload equality or explicit upper-bound join.
- Lambdas: creation-time effects = captures + allocation; body effects recorded as latent on the lambda's type scheme so call sites merge them.
- Publication: per-function summaries `{may_effects, completeness, dependency_fingerprint}` stored in the existing TLDR/immutable cache; `CompilerQueryContext` (`90.tools/query_api.spl`) gains `effects_at`/`effect_provenance` queries consumed by LSP hover, `simple inspect effects`, and MCP `simple_sem_query`.
- Unification rule: `35.semantics/param_effects/` and `30.types/type_system/effects.spl` are folded into or mapped onto the `EffectKind` row registry at integration points in `80.driver/driver_hir_pipeline_support.spl:50-51,403-447`; no third taxonomy survives (NFR-COR-01).

### 2.3 Typed endpoints and typestate (P4/P5)

- **Channels**: new `Sender<T>`/`Receiver<T>` types in `src/lib/nogc_sync_mut/concurrent/` created together by `channel<T>(capacity)`; both hold the channel id plus a phantom type parameter (marker `unit` types for payload binding). `send` returns `Result<(), SendError<T>>` carrying the message back on rejection; the legacy `Channel` class is re-expressed on top (compat shim with removal gate) after real callers migrate. `channel_from_id` unsafe import remains non-generic-forging: safe import requires runtime registration evidence.
- **TCP**: generic state parameters `TcpStream<R, W>` over existing runtime handles; `shutdown_write`/`close` consume and return the narrowed type; existing `tcp_state_can_send/receive` guards become the runtime backstop behind the static permissions. Invalid-send silent no-op and invalid-receive empty-text behaviors become typed errors as part of the wrapper (REQ-STATE-01), with the raw tuple API kept internal.
- **Sessions (P5)**: `Send<T, Next>`/`Recv<T, Next>`/`End` descriptor types in a new stdlib module; endpoint objects are linear (non-copyable) wrappers over channels; recursion via named protocol graph with bounded expansion.
- **Async**: cancellation/commit matrix from design §7.5 encoded in the endpoint contracts; async channel facade re-exports typed endpoints once the sync semantics land.

### 2.4 Analysis modes (P6)

- Build-mode gate keyed on existing build configuration: `debug`/`invest`/`ci` enable budgeted deep jobs (refinement solvers, protocol/alias exploration, MIR translation validation). Normal/release never schedule them; mandatory cheap checks (§9.2 of design) run in all modes.
- `invest` is configuration, not a keyword; CLI `simple check --mode invest --scope ... --budget-ms ...` routes to the same verifier entry points with a job budget and produces SDN reports (SDN-by-default rule).

### 2.5 One semantic service (P2/P6)

- Compiler-native facts only: `CompilerQueryContext` in `src/compiler/90.tools/query_api.spl` is the single source for hover (unit role/representation/suffix/dimension/predicate; effects + completeness + provenance; typestate), diagnostics, and versioned edit plans.
- CLI: new branches in `src/app/cli/_CliMain/main_and_help.spl` + `_cmd` rows in `command_registry.spl` for `inspect` and `refactor` (mirroring the `query` pattern at `run_commands.spl:639`).
- MCP: new `tool_entry` rows in `src/app/mcp/tool_table.spl` calling the same CLI/query operations.
- LSP: handlers in `src/lib/nogc_sync_mut/lsp/` consume the same query commands; unit/effect/typestate hover added beside `handlers/hover.spl`.
- Edits: reuse `WorkspaceEdit` + snapshot validation; the design's full transaction protocol is future work — until then, multi-file plans are applied file-by-file with per-file validation and no cross-file success claims (design §10.5).

## 3. Data-flow invariants

1. HIR types remain target-independent; layout/ABI facts live only in the `_TypeLayout`/MIR overlay.
2. Effect summaries never lose completeness status when cached; a timeout/unsupported result is `unknown`, never success.
3. A predicate omitted in release cannot justify optimization, niches, unchecked loads, or transitions (design §5.1).
4. Marker erasure never erases ownership/lifetime/transfer constraints (phantom-type rule).
5. Legacy and canonical spellings lower to identical semantic facts during the compatibility window; only version-gated promotion changes that.

## 4. Failure modes and degradation

- Unknown callee/foreign behavior → incomplete effect row → required-effect bounds reject, optional bounds warn; never silent purity.
- Deep-analysis timeout/cancel → `unknown` result, no success certificate, checked paths remain available.
- Stale snapshot/edit plan → validation failure with re-request, never partial-apply success claim.
- Backend cannot establish post-state (TCP half-close uncertainty) → explicit cleanup-only continuation or runtime-owned cleanup.

## 5. Risks

| Risk | Mitigation |
|---|---|
| Grammar ambiguity of contextual `unit` | Follow seed's contextual dispatch; positive/negative parser tests required (PARSE-01/02) before migration tooling |
| Effect unknown-marking breaks existing builds | Stage behind completeness warnings first; fail-closed only where a required bound exists |
| Channel API change breaks callers | Migrate real callers with previewed plans; shim with removal gate; never silent discard |
| Bootstrap cycle: compiler changes need new binary | Schedule bootstrap build deliberately (agent-8 notes); use admitted stage2/3 paths per minimal bootstrap guide; isolate caches |
| Scope creep (P5/P6 research features) | Land P1-P3 first as independent PRs; P4 follows; P5/P6/P7 separately gated |
