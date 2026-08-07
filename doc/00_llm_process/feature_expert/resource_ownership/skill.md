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
| REQ-MC-023 | (2026-08-07, this change) | `W-MC-RES-001 unwrapped_foreign_resource` lint landed — `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`, reuses `resource_families.acquire_verbs()`, wired through the WP-3 canonical policy resolver (allow moderate/strict/robust, warn critical). Text-level, intraprocedural, single-assignment heuristic (return/tail-expr/`self.field` escape only — no cross-call argument threading). 17/17, sabotage-verified. **LIVE as of 2026-08-07** (previously recorded here as DORMANT — corrected; probe: a bare acquire returned from a fn warns under `--profile=critical`, silent under `--profile=moderate`, silent when wrapped in an owning **or refcounted** class). **Over-fires**: 208 findings / 78 files over a 245-file sweep, mostly value constructors (`rt_string_new`, `rt_dir_create`→bool, `rt_atomic_int_load`→atomic read); must not go `deny` as-is, and the paired-release narrowing is unsound (fails open on `rt_io_tcp_socket_create`, `rt_cuda_module_load`). See `doc/08_tracking/bug/w_mc_res_001_overfires_verb_only_heuristic_2026-08-07.md` |
| WP-E | `794bbf6642f` | MIR drop edges for `iso`-wrapped resource-typed locals (new `MirInstKind.Drop` + `MirBuilder.emit_drop`), emitted at normal scope exit, an explicit `return`, and a `?` Err/None early-return arm; `.close()` on a resource place lowers straight to a consuming Drop (`method_calls_literals.spl`'s `lower_method_call`, checked ahead of resolution). Hand-built-HIR harness (mirrors LANE ISO1's `iso_move_pipeline_spec.spl`) driving `MirLowering.lower_function` directly and asserting on emitted `Drop` instructions — 5/5, sabotage-verified. Found and left open (not fixed, out of scope): lowering a trailing tail expression AFTER an already-terminated block (e.g. a mid-body `return` followed by more body) corrupts the block's finalized instruction list — a pre-existing MIR-lowering artifact, unrelated to resource semantics, worked around in the spec by giving the early-return case no trailing tail |
| WP-I | `(prior commit)` | Interpreter parity for resource drop/consuming-close, found narrower than the plan assumed: drop TIMING (implicit scope end, `return`, `?` early-return, `.close()`) is produced entirely by `MirLowering` — one implementation shared by every backend — so it was already identical under interpreter execution with zero interpreter-side code. The real gap was one level down: `compiler.interp.mir_interpreter`'s `MirInterpreter.execute_instruction` (`src/compiler/95.interp/mir_interpreter.spl`) had no arm for the new `MirInstKind.Drop` and fell through to `case _:` → `InterpError.UnsupportedOperation("unknown instruction")`, so ANY function containing a resource-typed local, or a `.close()` call, was uninterpretable after WP-E landed. Fixed with a no-op `Drop` arm (mirrors the existing `DebugValue`/`Nop` no-ops — no backend, including native codegen, wires a real release extern yet; that's WP-H). Acceptance: WP-E's own `resource_mir_drop_spec.spl` (5/5) is unaffected either mode since it never executes a function, so it's non-regression evidence, not the WP-I oracle; the real oracle is new `test/01_unit/compiler/resource/resource_interp_drop_spec.spl`, which drives `MirLowering.lower_function` then executes the result through `MirInterpreter.execute_function` — 3/3, sabotage-verified (removing the `Drop` arm turns all 3 red with `UnsupportedOperation`) |
| WP-K | *(this commit)* | `with ACQUIRE as NAME: BODY` scoped form, `src/compiler/10.frontend/core/parser_stmts.spl`. `with` is a soft keyword recognized ONLY at statement-start (`parse_statement`'s `TOK_IDENT` branch), resolved positionally against the pre-existing class-header `with Read, Write:` mixin form (`fn_struct_decls.spl`'s `parse_struct_or_trait_decl`) — the two are parsed by disjoint functions reached from disjoint call sites, so no token position is ever ambiguous. Desugars to one nested block: `val NAME = ACQUIRE ; BODY ; NAME.close()`, reusing WP-E's drop machinery for early exits (return/`?` inside BODY) and the appended `.close()` for normal fall-through. **Real grammar collision found and worked around**: `as` is ALSO the cast operator, consumed by `parse_expr()`'s `parse_unary` before this branch can see it, so `with ACQUIRE as NAME:` parses as `expr_cast(ACQUIRE, NAME-as-Type)` — unwrapped after the fact (gated on the very next token being `:`, via `named_type_name(expr_get_int(cast) - TYPE_NAMED_BASE)`) rather than looked for as a leftover token. **Real WP-E registration gap found and closed**: `resource_owned_locals` only registered a resource-typed function PARAMETER or a `val b = a` MOVE of an existing resource-owned place (`mir_lowering_stmts.spl`) — a FRESH acquire result (`val x = R.open(...)`, exactly what `with` desugars to) took the plain `emit_copy` branch and was never registered, so early-exit drops would have silently never fired for real `with`-bound resources. Closed by registering a fresh resource-typed binding too (same `mir_hir_type_is_resource` helper), gated on whichever HIR type actually got remembered on the local (inferred, or the declared `let_type` as fallback). Acceptance: parser-level `test/01_unit/compiler/resource/resource_with_scoped_spec.spl` (5/5, source-string harness via `parse_module_body()`, proves the collision resolution + desugared AST shape) + MIR-level `test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl` (4/4, hand-built-HIR harness proving close-on-fall-through, drop-on-return, drop-on-`?`-inside-BODY, and NO drop/registration when the ACQUIRE's own `?` fails first) — both sabotage-verified |
| WP-G | *(this session, 2026-08-07)* | Borrow-check enforcement of the 6 invariants in scope (design doc §8, invariants 1/2/3/6/7/8). Per-invariant: **inv 8** (`@R` requires `thread_safe: true`) already a hard `parser_error` since WP-B (`_FlatAstBridge/convert_nodes.spl`) — confirmed via existing `resource_ownership_sigil_spec.spl`, 6/6, no new code. **inv 2** (use-after-move) already worked with zero new code: a resource type is `HirTypeKind.Isolated(Named(sym))`, the same wrapper LANE ISO1's move machinery keys off — `resource_use_after_move_spec.spl`, 3/3, sabotage-verified (disabling `mir_hir_type_is_isolated` -> 2/3 failed). **inv 1 + inv 6** (exactly-once release; `close()` consumes) needed one new arm: `MirInstKind.Drop` fell through `analyze_instruction`'s catch-all with no move/consume fact recorded — added `case Drop(local): nll.record_move(...)` (`borrow_check/mod.spl`), reusing `record_move`'s existing double-move detection for both invariants at once. `resource_drop_exactly_once_spec.spl`, 6/6, sabotage-verified (disabling the arm -> 4/6). Also measured and documented a known, pre-existing SF1 over-approximation this arm inherits: two Drops of the same local on genuinely mutually-exclusive branches (WP-E's own independent per-exit drop edges) can false-positive, since the checker's block walk is linear, not CFG-path-sensitive — same accepted class of limitation as WP-F's Move handling. **inv 7** (`*R` forbids `mut` methods) was genuinely unimplemented (`resource_ownership_kind` written by WP-B, read by nothing) — new `MirLowering.mir_hir_type_is_shared_resource` helper (mirrors `mir_hir_type_is_resource` but for `Ptr(Named(sym))`, since `*R` lowers to plain `Ptr` at HIR lowering) plus a check in `lower_method_call` (`_MirLoweringExpr/method_calls_literals.spl`) that calls `self.error_fatal(...)` when an `InstanceMethod`'s own symbol carries `is_mutable: true` through a shared receiver. Only `*R` is covered — `@R`/`-R` erase to `HirTypeKind.Infer` at `hir_lowering/types.spl` before this pass ever sees them, so those two sigils have no HIR-level fact left to key a check on. `resource_shared_mut_method_spec.spl`, 3/3, sabotage-verified (disabling the `error_fatal` call -> 2/3 failed). **inv 3** (borrow pinning across foreign/blocking calls) left RED: `record_move` never consults the borrow set (only `moved_now`) and there is zero MIR/checker concept of a foreign-call-scoped borrow region — real region/lifetime infrastructure, correctly out of WP-G's single-spec scope per its own stated boundary. `resource_borrow_pinning_spec.spl`, 1/1 failing as expected (`0 passed, 1 failed`); full writeup `doc/08_tracking/bug/resource_borrow_pinning_not_enforced_2026-08-07.md` |
| WP-H | `51e08eb7ead` | `sffi_gen` resource-wrapper emitter (`src/compiler/90.tools/sffi_gen/resource_wrapper_gen.spl`): takes a `FamilyClassificationResult` (WP-D), generates an owning wrapper class with invalid-sentinel check, a static factory acquire method, borrowing methods, and a consuming `close()` with the one-shot double-close guard. **Template-only, hardcoded to the `rt_file*` family** — not yet a general per-family emitter; the `resource R` grammar path this would ideally target is still blocked on the seed (see "Your acceptance oracle is probably unreachable" below), so it targets the current opaque-handle pattern instead. Golden-file spec (`resource_wrapper_gen_spec.spl`), 5/5, sabotage-verified. WP-J's hand-authored wrappers below follow this exact generated shape rather than being run through the generator itself. |
| WP-J | `35889a86f4f` | Pilot migration of two real foreign-resource families to the WP-H wrapper shape, hand-authored (the generator is `rt_file*`-only per WP-H): `Image` (`src/lib/nogc_sync_mut/io/image_sffi.spl`, wraps `rt_image_*`, sentinel `handle == 0`) and `FileLock` (`src/lib/nogc_sync_mut/sffi/io.spl`, wraps `rt_file_lock`/`rt_file_unlock`, sentinel `handle == -1`). Both add a consuming `close()` with a one-shot double-close guard; old `load_image`/`free_image`/`ImageData`/`file_lock`/`file_unlock` kept as deprecated thin aliases so existing callers are unaffected. **Landing incident, now corrected:** this work was originally committed locally (2026-08-07) but never pushed; a separate, already-pushed commit (`7868b6ab6e2`) fixed a crash/live-fd risk in the two acceptance specs by removing their fabricated-handle `.close()` examples — but that commit's specs `use ...image_sffi.{Image, ...}` / `...sffi.io.{FileLock, ...}`, symbols that did not exist anywhere on `origin/main` at the time, since the actual wrapper classes were still sitting unpushed. `origin/main` was in a broken state (a spec importing a nonexistent symbol) until this commit landed the real classes. Found by checking file CONTENT on `origin/main`, not the local task tracker (which had already marked WP-J "completed"). Re-verified after landing: `image_sffi_resource_wrapper_spec.spl` 9/9, `file_lock_resource_wrapper_spec.spl` 6/6, both real runs against `origin/main`'s HEAD. Full write-up of the double-close testing gap that's still open: `doc/08_tracking/bug/image_wrapper_close_needs_live_handle_fixture_2026-08-07.md`. |

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
- RC lowering (WP-B). `sffi_gen` adapter generation (WP-H) is landed but
  template-only (`rt_file*` hardcoded) -- generalizing it to emit for
  arbitrary families from `FamilyClassificationResult` is still open, as is
  wiring WP-E's bare `Drop` marker to each resource's real
  `@sffi(release: ...)` extern at codegen (no backend, interpreter included,
  calls a real release extern from a `Drop` yet -- WP-I's interpreter arm is
  a no-op by design). WP-G (borrow-check enforcement of invariants
  1/2/3/6/7/8) is landed for 1/2/6/7/8 -- see the WP-G row above. Invariant 3
  (borrow pinning across foreign calls) remains genuinely unenforced; needs
  new region/lifetime infrastructure, tracked at
  `doc/08_tracking/bug/resource_borrow_pinning_not_enforced_2026-08-07.md`.
- WP-J only migrated 2 of the 85 census'd foreign-resource families
  (`Image`, `FileLock`), and both are hand-authored `class` wrappers with a
  manual `close()` guard -- NOT the `resource R` grammar itself, which
  remains unreachable from `src/**` until stage-3 self-host is unblocked
  (see "Your acceptance oracle is probably unreachable" above). The
  remaining ~83 families are unmigrated.
- WP-E's drop-edge placement is syntactic per-exit, not full NLL liveness:
  each real MIR exit (scope end, `return`, `?`) gets its own independent
  drop. WP-G's new `Drop`-arm move-recording (`borrow_check/mod.spl`)
  inherits SF1's linear, non-CFG-path-sensitive block walk as a result: two
  Drops of the same local on genuinely mutually-exclusive branches can
  false-positive as a double-drop -- measured and documented in
  `resource_drop_exactly_once_spec.spl`'s own "known limitation" block,
  same accepted class of over-approximation as WP-F's Move handling.
- REQ-MC-023 / `W-MC-RES-001` is **implemented and LIVE** (corrected
  2026-08-07 — it was previously recorded here as DORMANT, which is no longer
  true). Checker at
  `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`, wired in
  `90.tools/lint/_LintMain/lint_checks.spl`, registered `warn` under
  `critical` in `config_and_model.spl`. Verified by positive capability probe,
  not inference: a bare acquire returned from a fn produces
  `warning[W-MC-RES-001]` under `bin/simple lint --profile=critical`, stays
  silent under `--profile=moderate`, and stays silent when wrapped in either
  an owning class **or a refcounted class** — so "ownership **or** ref count"
  is already satisfied, incidentally, because the accept predicate takes any
  `TypeName(...)` constructor.
- **But it over-fires badly and must not be promoted to `deny` as-is**: a
  245-file sweep produces **208 findings across 78 files**, dominated by
  value constructors that name no resource (`rt_string_new`, `rt_array_new`,
  `rt_dir_create` → returns bool, `rt_atomic_int_load` → an atomic read).
  The verb-only text heuristic cannot tell a handle acquire from a value
  constructor without return-type information. The obvious narrowing
  (require a same-prefix paired release) is **unsound** — it would silence
  `rt_io_tcp_socket_create` and `rt_cuda_module_load`, i.e. fail open on real
  leaks. Full measurement, controls, and the unsoundness proof:
  `doc/08_tracking/bug/w_mc_res_001_overfires_verb_only_heuristic_2026-08-07.md`.
  A sound version needs to key on the declared handle type that
  `@sffi(handle: ...)` / `resource R` already carry (WP-A/WP-C's registry) —
  i.e. a semantic check, not a text scan.
