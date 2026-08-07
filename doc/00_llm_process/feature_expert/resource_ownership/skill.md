# Feature Expert: `resource` — origin-neutral ownership for foreign + native resources

**Docs:** research/architecture/design/plan under
`doc/{01_research,04_architecture,05_design,03_plan}/language/resource/`.
Companion feature page: `../iso_ownership/skill.md`. Assurance side:
`../mission_critical_robustness/skill.md` (REQ-MC-023 is the profile rule that
makes an unwrapped foreign handle a diagnostic).

## The idea
One nominal `resource R` declaration covers files, sockets, GPU buffers, DB
connections, locks and SFFI handles alike. Callers distinguish **ownership
semantics**, never implementation origin — there is deliberately no public
`Foreign<File>` / `Native<File>` / `SffiHandle<File>`. Plain `R` = unique affine
owner, `*R` = shared RC, `@R` = atomic RC, `-R` = weak. `close()` is a consuming
drop; methods borrow by default.

## Landed so far (2026-08-07)

| WP | Commit | What |
|---|---|---|
| WP-A | `1a6a7da02f6`, `7c60ee34bc0` | `resource` decl + `@sffi` decorator parse. **Soft keyword** — see below. Regression spec 18/18, sabotage-verified |
| WP-C | `286aa95c6f7` | All seven `@sffi` keys (`prefix`, `handle`, `invalid`, `retain`, `release`, `sharing`, `thread_safe`) round-trip into `compiler.frontend.resource_registry`, per-resource, reset per parse. 8/8, sabotage-verified |
| WP-D | `57da6077b69`, `45c0f068163` | Fail-closed convention inference (`resource_families.spl`): classifies acquire/release/retain verbs from extern names, returns an explicit error (never a guess) on ambiguity. Now 17/17 — the residual failure was `load` missing from the acquire-verb catalog (`rt_image_load` classified as method, family left acquire-less). Census coverage across the 85 families is unmeasured — Appendix A only samples, doesn't enumerate |
| REQ-MC-023 | (2026-08-07, this change) | `W-MC-RES-001 unwrapped_foreign_resource` lint landed — `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`, reuses `resource_families.acquire_verbs()`, wired through the WP-3 canonical policy resolver (allow moderate/strict/robust, warn critical). Text-level, intraprocedural, single-assignment heuristic (return/tail-expr/`self.field` escape only — no cross-call argument threading). 17/17, sabotage-verified. **DORMANT**: deployed `bin/simple lint` predates this source; unit-spec (`test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl`) is the acceptance oracle until the next lint-binary redeploy (WP-3.5) |
| WP-E | `794bbf6642f` | MIR drop edges for `iso`-wrapped resource-typed locals (new `MirInstKind.Drop` + `MirBuilder.emit_drop`), emitted at normal scope exit, an explicit `return`, and a `?` Err/None early-return arm; `.close()` on a resource place lowers straight to a consuming Drop (`method_calls_literals.spl`'s `lower_method_call`, checked ahead of resolution). Hand-built-HIR harness (mirrors LANE ISO1's `iso_move_pipeline_spec.spl`) driving `MirLowering.lower_function` directly and asserting on emitted `Drop` instructions — 5/5, sabotage-verified. Found and left open (not fixed, out of scope): lowering a trailing tail expression AFTER an already-terminated block (e.g. a mid-body `return` followed by more body) corrupts the block's finalized instruction list — a pre-existing MIR-lowering artifact, unrelated to resource semantics, worked around in the spec by giving the early-return case no trailing tail |
| WP-I | `(prior commit)` | Interpreter parity for resource drop/consuming-close, found narrower than the plan assumed: drop TIMING (implicit scope end, `return`, `?` early-return, `.close()`) is produced entirely by `MirLowering` — one implementation shared by every backend — so it was already identical under interpreter execution with zero interpreter-side code. The real gap was one level down: `compiler.interp.mir_interpreter`'s `MirInterpreter.execute_instruction` (`src/compiler/95.interp/mir_interpreter.spl`) had no arm for the new `MirInstKind.Drop` and fell through to `case _:` → `InterpError.UnsupportedOperation("unknown instruction")`, so ANY function containing a resource-typed local, or a `.close()` call, was uninterpretable after WP-E landed. Fixed with a no-op `Drop` arm (mirrors the existing `DebugValue`/`Nop` no-ops — no backend, including native codegen, wires a real release extern yet; that's WP-H). Acceptance: WP-E's own `resource_mir_drop_spec.spl` (5/5) is unaffected either mode since it never executes a function, so it's non-regression evidence, not the WP-I oracle; the real oracle is new `test/01_unit/compiler/resource/resource_interp_drop_spec.spl`, which drives `MirLowering.lower_function` then executes the result through `MirInterpreter.execute_function` — 3/3, sabotage-verified (removing the `Drop` arm turns all 3 red with `UnsupportedOperation`) |
| WP-K | *(this commit)* | `with ACQUIRE as NAME: BODY` scoped form, `src/compiler/10.frontend/core/parser_stmts.spl`. `with` is a soft keyword recognized ONLY at statement-start (`parse_statement`'s `TOK_IDENT` branch), resolved positionally against the pre-existing class-header `with Read, Write:` mixin form (`fn_struct_decls.spl`'s `parse_struct_or_trait_decl`) — the two are parsed by disjoint functions reached from disjoint call sites, so no token position is ever ambiguous. Desugars to one nested block: `val NAME = ACQUIRE ; BODY ; NAME.close()`, reusing WP-E's drop machinery for early exits (return/`?` inside BODY) and the appended `.close()` for normal fall-through. **Real grammar collision found and worked around**: `as` is ALSO the cast operator, consumed by `parse_expr()`'s `parse_unary` before this branch can see it, so `with ACQUIRE as NAME:` parses as `expr_cast(ACQUIRE, NAME-as-Type)` — unwrapped after the fact (gated on the very next token being `:`, via `named_type_name(expr_get_int(cast) - TYPE_NAMED_BASE)`) rather than looked for as a leftover token. **Real WP-E registration gap found and closed**: `resource_owned_locals` only registered a resource-typed function PARAMETER or a `val b = a` MOVE of an existing resource-owned place (`mir_lowering_stmts.spl`) — a FRESH acquire result (`val x = R.open(...)`, exactly what `with` desugars to) took the plain `emit_copy` branch and was never registered, so early-exit drops would have silently never fired for real `with`-bound resources. Closed by registering a fresh resource-typed binding too (same `mir_hir_type_is_resource` helper), gated on whichever HIR type actually got remembered on the local (inferred, or the declared `let_type` as fallback). Acceptance: parser-level `test/01_unit/compiler/resource/resource_with_scoped_spec.spl` (5/5, source-string harness via `parse_module_body()`, proves the collision resolution + desugared AST shape) + MIR-level `test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl` (4/4, hand-built-HIR harness proving close-on-fall-through, drop-on-return, drop-on-`?`-inside-BODY, and NO drop/registration when the ACQUIRE's own `?` fails first) — both sabotage-verified |

## Four things you will otherwise re-derive painfully

### 1. Your acceptance oracle is probably unreachable
**Do NOT write acceptance as "real source using `resource` syntax, in a spec
file."** `bin/simple test` re-execs a child **Rust seed** whose parser reads the
spec file's own module-level syntax. No pure-Simple frontend change can make that
spec parse.

Proven by **positive control**, not inference: a spec containing `layer
ProbeLayer` — an already-landed, working pure-Simple soft keyword — fails
identically with `function 'layer' not found`.

Use the **source-string harness** (the `const_spec.spl` shape): feed a source
string to `parse_module_body()` and assert on the resulting AST/registry. That is
what both passing specs above do.

By the same mechanism, **production `src/**` code cannot adopt the syntax yet** —
the seed compiles the tree. Land the pipeline behind the syntax; migrate the 85
foreign-resource families after stage-3 self-host.

### 2. `resource` MUST stay a soft keyword
There are **112** identifier uses of `resource` in `src/` (measured by
identifier-position regex; raw word count 905 includes comments and `resource_*`
compounds), **including inside the compiler's own source**. A hard/reserved
keyword breaks the compiler's own rebuild. WP-A implemented it as a soft keyword,
which makes the break structurally impossible. Related: `layer` and `cli` use
**no token constant at all** — an earlier plan note claiming "the new token is
222" was wrong, and adding one is exactly the risk being avoided.

### 3. Ownership strategy is NOT selected by the defining tier
The natural-sounding rule "`nogc_*` → affine, `gc_*` → RC" is **refuted**.
Strategy comes from **per-resource `@sffi` metadata** (`sharing:`, retain/release
presence) **plus the use-site sigil** (`R`/`*R`/`@R`) — architecture doc §3 ("RC
activates only when the program writes `*R`/`@R`") and §7 (`@R` gated on the
resource's own `thread_safe:`). Tier only constrains **legality**:
`nogc_async_mut_noalloc` forbids allocation, so wrapper-RC — which needs a
control block — is illegal there. Corroborating measurement: that tier declares
**zero** release-family externs.

### 4. Census and lexing gotchas
- **85** distinct `_free`/`_close`/`_destroy`/`_release`/`_unref`/`_dispose`
  extern families in owned code (vendor excluded, `ffi/`↔`sffi/` twins deduped).
  Per-tier declaration sites: `nogc_sync_mut` 100, `app/io` 21,
  `nogc_async_mut` 12, `gc_async_mut` 7, `common` 4,
  `nogc_async_mut_noalloc` **0**. Full table: design doc Appendix A.
- **`invalid: -1` lexes as TWO tokens.** Handling only single tokens silently
  drops the sign. WP-A folds the leading `-` into the value text; assert the
  exact string (`"-1"`), never just non-emptiness.
- **`*T` in type-annotation position already parses** — WP-B is smaller than the
  plan assumed.

## Still open
- RC lowering (WP-B); borrow-check enforcement of exactly-once/use-after-
  consume (WP-G, builds on WP-E's drop edges); `sffi_gen` adapter generation
  (WP-H, would wire WP-E's bare `Drop` marker to each resource's real
  `@sffi(release: ...)` extern).
- WP-E's drop-edge placement is syntactic per-exit, not full NLL liveness:
  each real MIR exit (scope end, `return`, `?`) gets its own independent
  drop; distinguishing which exit a given RUN actually takes is WP-G's job.
- REQ-MC-023 / `W-MC-RES-001` is **implemented but DORMANT**: the checker exists
  (`src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`, wired in
  `90.tools/lint/_LintMain/lint_checks.spl`, registered `warn` under `critical`
  in `config_and_model.spl`), but the deployed `bin/simple lint` binary predates
  it, so it fires for nobody until the lint redeploy (WP-3.5). The unit spec is
  the only acceptance oracle today — 17/17, sabotage-verified (stubbing
  `_ufr_is_acquire_name` → `17 total, 10 passed, 7 failed`).
