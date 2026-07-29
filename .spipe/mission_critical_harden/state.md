# Feature: Simple Mission-Critical Hardening

## Raw Request
Goal set: spipe dev skill, harden simple with the parallel simple harden plan
(mission-critical robustness vs Rust/Ferrocene; first merge batch started with
parallel agents 2026-07-28).

## Task Type
code-quality / compiler-hardening

## Refined Goal
Execute the mission-critical robustness plan so that the four requirement pillars
(semantic primitive-free APIs, stable semantic md links, Lean generation without stub
paths, verified ISA/GPU lowering) rest on repo-verified ground truth, with each batch
landed via disjoint-ownership parallel agents and fail-closed gates.

## Plan Docs (authoritative)
- Research + verified audit: `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md` (§13 = agent-verified file:line ground truth)
- Wave/lane plan: `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`

## Acceptance Criteria (Batch 1 — first merge batch)
- **AC-1 (primitive table):** ONE canonical primitive table (incl. `bool`) consumed by
  all .spl checkers; parity spec guards drift vs the Rust seed list
  (`rules.rs:6-8`). The `primitive_api.spl:3` header/`:20` table contradiction gone.
- **AC-2 (newunit):** `unit_registry.spl:253-282` scaffold replaced — parsed `newunit`
  declarations observable in the registry, spec-proven; `newtype` suggestion typo fixed.
- **AC-3 (CUDA layout):** `cuda_backend.spl` field offsets/loads/GEP/cast use
  `cuda_type_mapper` sizes (`:272-295`) instead of hardcoded 8-byte/i64 assumptions;
  PTX `.version` a named constant, no longer stale 7.8; existing CUDA/PTX specs green.
- **AC-4 (sorry gate):** `verify/checker.spl:246-254` `_count_sorry` token/comment-aware;
  spec proves comment prose and identifiers no longer false-positive, real `sorry` flagged.
- **AC-5 (SymbolId):** stable 128-bit SymbolId library + short-fingerprint collision
  detection landed as a self-contained module with red/green specs; no integration yet.
- **AC-6:** every lane records `pass` / `blocked` / `filed` with evidence; no lane
  self-declares production-ready — orchestrator verifies against the live tree.
- **AC-11 (compiler/loader default = robust-at-warn, user decision 2026-07-28):**
  native build + module loading default to the `robust` profile with rules at WARN
  severity (migration window); escalation to error is a later backward-compat step.
  Plan lane: PR2 `profile-rename-and-defaults` (queues behind R2) implements rename
  + aliases + loader default; PE implements the engine flag + resolution order.
- **AC-10 (profile ladder rename + engine axis, user approved 2026-07-28):**
  profiles renamed `moderate|strict|robust|critical` (old `lib`/`reliable`/
  `mission-critical` = deprecated aliases w/ warn-once); `robust` = Rust-level
  (all escapes denied); engine axis explicit `--engine=interpreter|jit|native`
  with INTERPRETER as new default for run/test (JIT opt-in). Rename lane queues
  behind R2 (config_and_model.spl ownership); engine flag lands with PE lane.
- **AC-9 (profile-aware execution, user design 2026-07-28):** REQ-MC-012 —
  interpreter is a first-class default engine and `run`/`test` accept
  `--profile=moderate|lib|reliable|mission-critical` so tests execute under a chosen
  profile (pre-run lint fail-closure + profile-gated runtime checks). Verified absent
  today (lint-only). Batch-3 lane PE; launches after R2's profile skeleton lands
  (same-file ownership on config_and_model.spl).
- **AC-8 (no-internal-primitives, user decision 2026-07-28):** `W-MC-VAL-001
  bare_primitive_internal` lands per REQ-MC-011 — firmware-style: bare primitive
  locals/literals warned in the NEW `mission-critical` lint profile (allow elsewhere;
  deny at profile v2 for backward compat). Domain annotation (`val x: DurationMs = 1`)
  or unit-suffix literal (`val x = 1_s`) satisfies it. This also creates the
  mission-critical profile skeleton in lint config.
- **AC-7 (const-ref, user decision 2026-07-28):** `W-MC-REF-001` lint lands — WARN when
  a function mutates a parameter not marked `mut` (reassignment, index-assign, or
  known-mutating method call on it); receiver mutation already gated by `me`.
  Warning-level in all tiers now; escalation to deny in mission-critical is a later
  profile-v2 change, NOT this batch. Spec proves warn-on-mutation and silence for
  `mut`-annotated params.

| DS2 `diagnostic-v1` | **ACCEPTED 2026-07-28.** Additive-only (orchestrator-verified: only 2 new untracked files under `00.common/diagnostics/`, zero modifications to `span.spl`/`diagnostic.spl`/`__init__.spl`). Closes the pure-Simple↔Rust-seed diagnostic drift: `code` promoted from optional to **required** (stable codes guaranteed), `help` as a list, **per-label `file`** so one diagnostic can span multiple files directly (the Rust seed only carries one file per diagnostic + a separate SourceRegistry), recursive `children`, `macro_trace`, and `DiagnosticFix`/`FixReplacement`/`FixConfidence(Safe|Likely|Uncertain)` ported from the seed's `EasyFix`. Self-contained JSON renderer, no serde. **Brace landmine correctly avoided:** the renderer never writes a literal `{`/`}` in a Simple string — it builds them via `char_from_code(123/125)`, sidestepping the interpolation bug filed earlier today. (My scan flagged 1 "risky" literal brace; on inspection it is a comment explaining the hazard, not code.) **3/3 passed, exit=0**, 27 assertions on rendered content, and the agent independently confirmed non-vacuity by rendering real JSON through `bin/simple run`. Deferred by design: LSP/SARIF renderers, `__init__.spl` re-export, and migrating existing emitters to DiagnosticV1. | orchestrator review 2026-07-28 |

| PR2 `profile-rename` | **ACCEPTED 2026-07-28** (AC-10 + AC-11, user-approved). Ladder renamed `Lib→Strict`, `Reliable→Robust`, `MissionCritical→Critical`, `Moderate` unchanged. `parse_lint_profile` takes new names first, then falls through to deprecated aliases `lib`/`reliable`/`mission-critical`/`mission_critical` → same variant. **Warn-once done correctly:** module-level `var _DEPRECATED_PROFILE_ALIAS_WARN_COUNTS: Dict<String,i64>` keyed by exact old spelling — orchestrator-verified it is NOT a struct field, which would have silently never persisted (the value-type copy defect that killed the whole safety checker). Uses `contains_key` per the native-Dict rule. Test-only accessor `deprecated_profile_alias_warn_count(old)` makes the fires-once contract directly provable instead of log-scraping. Engine-default resolution added (`InterpreterOrJit`→moderate, `CompilerLoader`→robust with every `deny` capped to `warn` via `_cap_at_warn`); **nothing escalated to error**, per the migration-window decision. `--engine=` CLI plumbing remains the separate PE lane. Call sites updated: `bare_primitive_internal_spec` (used old enum variants directly — would not compile), `entry_and_fixes.spl` help text, `lint_cli_option_validation_contract_check`. **`Results: 16 total, 15 passed, 1 failed`, exit=1 — the `Failed: 1` is PHANTOM**, and the agent proved it the right way: reverted BOTH files to pristine `main` HEAD and reproduced the identical phantom with none of its code present (pre-existing `test_runner_phantom_failed_after_all_examples_pass_2026-07-20.md`, now logged as a new confirmed instance rather than worked around). Per-example tally is 15/15 genuine. `git stash` used for that isolation was dropped — orchestrator confirmed no residue (the 3 stashes present belong to other sessions, dated 2026-07-26). **Known gap, deliberately left:** `doc/07_guide/language/strictness_tiers{,_tldr}.md` still document the old 3-tier `moderate\|lib\|reliable` naming and omit `critical` entirely — a real doc rewrite, flagged rather than half-fixed. | orchestrator review 2026-07-28 |

| DS5 `mir-span-thread` | **ACCEPTED 2026-07-28, with a finding that outranks the lane itself.** All **19** `emit_*` sites now stamp `span: self.current_span` instead of `nil` (orchestrator-verified: 22 `current_span` refs, exactly **2** `span: nil` left — both correctly out of scope: the fresh-builder default at :64 and a dead-path fallback in `end_function`). Threading uses a save/restore wrapper around `lower_expr`/`lower_stmt` (bodies renamed to `*_impl`), giving correct stack discipline so a compound node recovers its OWN span after operands push/pop theirs. Spec asserts exact line numbers on 3 Const + 2 BinOp — including that the outer BinOp gets 50 back rather than leaking the last child's 40, which is the real test of save/restore, not a lazy non-nil check. **1/1 passed, exit=0.** **THE FINDING:** driving the REAL `parse_full_frontend → HirLowering → MirLowering` pipeline, `HirFunction.span` is the exact zero `Span(0,0,0,0)`. Orchestrator confirmed structurally — **neither `HirFunction(` site in `declaration_lowering.spl` (:78, :380) assigns `span` at all**, and `hir_types.spl` uses `Span.empty()` at :464/:515/:578/:697. So DS1 (span truth), DS3 (DWARF), DS5 (MIR threading) and DS2 (label-per-file) are each individually correct and ALL terminate at this one upstream hole; every source location degrades silently to line 0 rather than failing loudly. Filed `hir_lowering_never_populates_function_spans_2026-07-28.md` — **this is now the highest-leverage next lane**, since fixing one gap activates four landed ones. Note a hand-built-HIR spec PASSES against this bug, which is why it stayed invisible; the guard must parse real source text. | orchestrator review 2026-07-28 |

| SE1 `safety-enforce` | **ACCEPTED after orchestrator redesign 2026-07-28.** The safety pass now ENFORCES, not just reports: `run_safety_warn_pass(ctx, ...)` routes each diagnostic into the compile context at profile-gated severity — `SIMPLE_SAFETY_PROFILE` unset/moderate/strict → Advisory (log-only, pre-SE1 behavior byte-identical), robust → `ctx.add_warning` (migration window, can never fail a build), critical → `ctx.add_error` (Rust-parity, fails the build). Deprecated aliases map to their new tier's severity (`reliable`→Warn, `mission-critical`→Deny). The pass now also RUNS when severity is enforcing, without needing the `SIMPLE_SAFETY_WARN=1` log opt-in. `CompileContext` is a `class` (driver_types.spl:34), so ctx mutations persist — checked, since a struct here would have silently re-killed the pass. **Two orchestrator repairs after the agent died at its session limit:** (1) the agent's `driver_safety_severity.spl` imported `compiler.tools.lint.main` — an upward 80.driver→90.tools layer dependency AND the trigger of a newly-found interpreter bug: executing lint-main's graph then `parse_full_frontend` in one session deterministically fails `semantic: cannot convert dict to int` (minimal A/B: import alone harmless, ONE executed `parse_lint_profile` call sufficient; filed `interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`). Rewritten self-contained: severity mapped directly from the profile NAME incl. frozen deprecated aliases, mirroring not importing `parse_lint_profile`. (2) disk `driver.spl` was **223 lines behind origin** (origin had a newer stage4-streaming iteration) — committing it would have reverted that work; SE1's hunks were re-applied onto origin's version via scripted anchored edits (each anchor asserted unique), and `driver_types.spl`'s stale disk copy (would have reverted coverage-config + `authored_path`) restored to origin untouched. Spec **12/12, exit=0**; parse-check clean. **Pre-existing, confirmed by origin's own docstring:** SafetyChecker only ever constructs `InlineAsmOutsideUnsafe` — the raw-pointer/FFI variants are declared but never built, so enforcement currently bites on inline-asm only; wiring those two rules is the natural SE2 follow-up. | orchestrator redesign 2026-07-28 |

| SE2/SE2b `safety-rules` | **ACCEPTED 2026-07-29, 5/5 exit=0 (orchestrator re-ran).** SE2's implementation survived its weekly-limit kill (swept to origin by a concurrent sync): `safetychecker_flag_callee` wires RawPointerOutsideUnsafe (rt_ptr_*/rt_alloc/rt_free/ptr_add*/ptr_sub* prefix list) + UnsafeFfiOutsideUnsafe (module-local extern fns) into the call walk. SE2b found why raw-pointer still returned 0: **`safetychecker_check_stmt` matched NONEXISTENT HirStmtKind variants `Val`/`Var`/`AssignOp`** — the real enum has `Let`/`Assign(target,op,value)`/`Block` — and the dead arms fell to `case _: pass`, so **every `val`/`var` initializer expression was never walked**. FFI only passed because its fixture used a bare statement call (`case Expr` worked). Fixed to real variants + added previously-unhandled `Block` recursion; `Assign` arity corrected (latent, untested). **Same compiler landmine family as `option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`: matching an undeclared variant name is silently accepted instead of being a compile error — third structurally-dead-code defect this campaign caused by silent pattern acceptance.** Orchestrator checked the remaining `case Var(_)` at :434 — legit (`HirExprKind.Var`, leaf). Blast radius (agent estimate, advisory): ~51 files call raw-ptr primitives with no `unsafe` token; extern-fn upper bound 1484 files but loose (rule needs same-module call+declare). | orchestrator verify 2026-07-29 |

| SYM1 `hir-symbol-table` | **CLOSED as not-reproducible, guard landed (2026-07-29).** Full-path trace: `declare_module_symbols` pre-declares every fn in MODULE scope (one define each); `SymbolTable.define` only first-write-short-circuits type kinds, Function always inserts; `lower_function` reuses the predeclared id. Bug-doc scenario re-run 3 ways × ~6 runs — every fn resolved distinctly. Most plausible original cause: `Dict.get()` flake at `hir_types.spl:286` `scope.symbols.get(name)` (documented native pitfall), already being hardened by another lane's RED `symbol_table_dict_get_source_spec.spl` — SYM1 correctly did NOT touch `hir_types.spl` to avoid clobbering it. Guard spec `hir_symbol_table_all_functions_spec.spl` (real 3-fn source, full pipeline) **1/1, exit=0**; regressions span-populate 2/2, mir-span 1/1. | orchestrator verify 2026-07-29 |
| RT1 `runner-unblock` (unplanned, orchestrator) | **FIXED + verified 2026-07-29.** A concurrent session's uncommitted monitor-timeout WIP in 4 runner files broke EVERY `simple test` invocation: `if monitor_timeout != "0" and to_int(monitor_timeout) < ...` throws on unset env because `to_int("")` throws and **the interpreter evaluates both sides of `and`** (no short-circuit) — and exporting the var didn't help (plausibly the documented interp `env_get` name-collision hijack). Fixed forward at all 4 sites (nested `if`, unset → set-to-effective-timeout, preserving their intent); known-green spec back to 7/7 with the var explicitly unset. Note: this made `bin/simple test` globally red for a window on 2026-07-29 — any "spec failed" observation from that window is suspect. | orchestrator fix 2026-07-29 |

| DS7 `crash-native` | **ACCEPTED 2026-07-29 — honest-subset delivery, exactly as briefed.** Inventory first (verified in source, not assumed): `rt_install_crash_handler` (runtime.c:1921) already installs an ALWAYS-ON async-signal-safe SIGSEGV/SIGBUS handler (raw write + backtrace_symbols_fd, `_exit(128+sig)`) auto-called from `spl_init_args` — but SIGABRT uncovered, `ucontext` (registers) received and DISCARDED, and none of it reachable from .spl. **Agent corrected the orchestrator's brief:** RingBackend + accessors were module-INTERNAL, not exported as assumed — added `ring_backend_level_at` and exported the family (log.spl delta +21/−0 pure additive, DS4 wrap intact, log_text_dispatch still 5/5). Delivered: `src/lib/nogc_sync_mut/crash/crash_bundle.spl` CrashBundleV1 (version, build_id honestly `""` — no BuildId manifest exists, timestamp, pid, fault_kind, message, source_location, trailing N ring records via `log_text_from_handle`), SDN serialization, write/read-back. **5/5 exit=0.** Extern gap FILED not stubbed: `crash_signal_bundle_extern_gap_2026-07-29.md` names the exact rt_* signatures (crash scratch register/len/read, handler-with-abort) and why signal-context can't call into interpreter/GC. Guide roadmap corrected "Planned"→"Partial" with citation. Real SIGSEGV→bundle capture blocked on that runtime work. | orchestrator verify 2026-07-29 |

## VCS state at handoff (2026-07-28) — READ BEFORE PUSHING

**`scripts/check/check-no-conflict-tree-push.shs` exits 1: DO NOT PUSH yet.**

Six commits sit in a conflicted chain. **The conflict ROOT is NOT this
campaign's work** — it is `feat(ui): add adapter and vision ui access sidecars`
(`5ff78c368048`), from a parallel session, conflicted in:
`doc/{02_requirements,04_architecture,05_design}/…/ui_access_protocol.md`,
`doc/06_spec/app/os/feature/ui_access_protocol_spec.spl`,
`doc/07_guide/tooling/{mcp,ui_access}.md`, `src/app/ui.test_api/handler.spl`,
`src/os/services/llm/{mcp_os_server,tool_registry}.spl`,
`test/system/ui/ui_access_contract_spec.spl`.

This campaign's five commits are **descendants** that inherited the marker.
Verified: each has **zero conflicts in its own files** (span/log/safety_checker/
llvm_ir_builder/parser_stmts all clean), real git trees (not `.jjconflict-*`
shells), and no leaked `<<<<<<<` markers. Content spot-checked via
`git cat-file` in the committed trees. **Nothing has been pushed.**

**Deliberately NOT resolved by this session.** Per `.claude/rules/vcs.md` the
fix is root-first, but that root is another session's in-flight work in UI/MCP
files this session does not own. Resolving it blind is exactly the documented
clobber risk ("origin already supersedes you… diff BOTH directions"). The owner
of the UI sidecar work should resolve `5ff78c368048`; descendants then auto-
rebase and the guard should go green. Re-run the guard taking `$?` from the
**script**, not through a pipe — piping to `tail` reports the pipe's exit and
turned this exact failure into a false "exit=0" once already today.

**Lock contention note:** `.git/index.lock` was held for ~25 min by a long-
running stage4 native-build probe (`native_probe/current-overlay-full-cli-fresh3`),
which pins `git rev-parse HEAD` to a fixed sha as a precondition — landing
commits during that probe may invalidate its baseline. Two removals were done
only after verifying `-mmin +5` staleness with no holder via pgrep/lsof/fuser.

## Follow-up opened by SF2 (orchestrator, 2026-07-28)

**SF2 made the safety pass REPORT; it still cannot ENFORCE.** Blast-radius check
after the `struct`→`class` fix: `driver.spl:1355-1381` `run_safety_warn_pass`
"pushes NOTHING to the compile context — the caller logs the result — so it can
never fail a build." So resurrecting the pass breaks no existing build (good),
but the three rules it now actually emits (`InlineAsmOutsideUnsafe`,
`RawPointerOutsideUnsafe`, `UnsafeFfiOutsideUnsafe`) remain advisory text.

For a Rust-parity claim this is only half the fix: Rust's equivalent is a hard
error, not a log line. The remaining work is to route these diagnostics into the
compile context at profile-gated severity — WARN under `robust` (per AC-11's
migration window), DENY under `critical`. That is a natural PR2/PE-adjacent
lane, not a new invention: the profile plumbing those lanes add is exactly what
the severity gate needs.

**Also note:** the effect of SF2's fix is NOT observable through `bin/simple`
today. `bin/simple` is the Rust SEED (`--version` prints the seed banner), whose
own pipeline does not run `src/compiler/**.spl`. Both SF2's revived pass and
DS3's DWARF wiring only take effect after a bootstrap redeploy — so neither has
a measurable repo-wide blast radius until then, and any "no errors appeared"
observation before redeploy is vacuous.

## Scope Exclusions (Batch 1)
A1 recursive semantic checker (starts after AC-1+AC-2 land); GPU intrinsic structural
IDs; `gpu_portable_compute` value-type widening; Lean generator stubs (C2-C5); md-link
lint/LSP/rename (B2-B5); ISA registry; Rust ledger. All scheduled in later batches per
the wave plan.

## Cooperative Review
- Lane P `primitive-table`: unify tables + bool (owns `src/compiler/35.semantics/lint/**` primitive files, `query_lint.spl` primitive fns, fix rule).
- Lane N `newunit-registry`: registry scaffold + typo (owns `src/compiler/30.types/units/**`).
- Lane G `cuda-layout`: type-mapper wiring + PTX version (owns `backend/cuda_backend.spl`, `backend/cuda/**`).
- Lane S `sorry-matcher`: token-aware counter (owns `src/compiler/90.tools/verify/checker.spl`).
- Lane B1 `symbol-id`: new self-contained module + specs.
- Merge owner: root orchestrator (this session). Agents DO NOT commit; orchestrator
  reviews diffs, runs gates, commits in dependency order.
- **Tiering (user directive 2026-07-28):** implementation work runs on SMALL agents
  (haiku = mechanical/finishing, sonnet = judgment/debugging); the HIGHER model
  (orchestrator) reviews every lane's diff + evidence before acceptance. No lane is
  accepted on its own report alone.
- Fail-fast placeholders only; no `skip()` without approval; reproduce-first specs
  where a defect is being fixed.

## Runtime Boundary Decision
- `runtime_need`: none — lint/registry/codegen/tooling work, no new externs.
- `facade_checked`: yes; specs use `std.io_runtime` facades.
- `chosen_path`: `reuse-facade`.
- `rejected_shortcuts`: no text-scanner "semantic" claims; no mass-suppression if bool
  detection fires on repo code (gate via existing rule levels + report); no golden
  fakery for PTX version bumps.

## Lane Ledger (live, 2026-07-28)

| Lane | State | Key evidence |
|---|---|---|
| P `primitive-table` | **done, orchestrator-verified structure** — canonical `primitive_types.spl` (11 types incl. bool, fn-based to dodge MODINIT001 native-zeroing); 3 .spl consumers import it; parity spec 4/4 agent-side; zero new lint errors (COLL006 pre-existing). Orchestrator parity-spec re-run pending (runner contention) | agent report 2026-07-28 |
| N `newunit-registry` | **done, VERIFIED GREEN** — full slice on disk (parser hook `newunit_register`, accessors types.spl +40, registry builder rewrite); orchestrator finished: `newtype`→`newunit` typo fix, `has()` rewritten to real bool (found `.?` returns Option PAYLOAD not bool on BOTH engines — filed `option_predicate_returns_payload_not_bool_2026-07-28.md`), spec rewritten to match-based assertions; **official `bin/simple test`: 5 examples, 0 failures, exit=0** (09:31 UTC) | orchestrator verify 2026-07-28 |
| G `cuda-layout` | **done, specs deferred on host load** — cuda_backend real-typed aggregate/field/GEP/cast via type_mapper w/ loud WARN fallbacks (Struct/Enum-by-SymbolId stays fallback: symbol table not carried in backend — filed as follow-up); `PTX_ISA_VERSION="8.0"` constant; goldens 7.8→8.0 (zero refs left in test/); lint 0 errors; smoke green. Full CUDA specs must re-run when host quiet (was load ~50, 186 simple procs) | agent report 2026-07-28 |
| S `sorry-matcher` | **done, SSpec blocked-on-runner** — `checker.spl:246-353` token-aware (strips `--`, nested `/- -/`, string bodies; Lean ident-boundary; counts sorry+admit); direct-driver 9/9 PASS; corpus scan 93 .lean files flagged=0 (was 35 false-positives); lint 0 errors. Official SSpec re-run needed when runner unblocks (4 attempts, 0 output, runner contended). Side-find: COLL006 type-blind on i64 accumulator in while loop (`collection_patterns.spl:368-393`) — file as linter bug | agent report 2026-07-28 |
| B1 `symbol-id` | **done, spec run pending host quiet** — `src/compiler/35.semantics/symbol_id/{stable_id,index,__init__}.spl` + 18-example spec; 128-bit sha256-truncated id (schema v1, tagged-field hash, no line/col/body inputs by construction); short fingerprint 12-hex + collision APIs (error, never guess); depth-aware `normalize_signature` drops names/defaults; index avoids Dict.get/len pitfalls; lint 0 errors. Spec re-run needs 900s+ budget when load drops (was 47-57) | agent report 2026-07-28 |
| A1 `semantic-checker` | **done, test-runner path blocked-on-runner** — `semantic_api/{type_walk,checker,__init__}.spl`: recursive walker over flat typed-Node AST (arena tags PROVEN lossy — Option<i32> collapses to TYPE_OPTION, unrecoverable), MC-API-001/002/003, no math exemption, newunit-aware via registry; alias hook fail-open w/ loud gap comment (no alias registry exists — follow-up); enums emit nothing (payloads discarded — A4 prereq confirmed); 16 examples 0 failures direct-driver; src lint clean. Standalone — pipeline wiring is a later serialized step | agent report 2026-07-28 |
| SF1 `borrow-feed` | **GOAL NOT ACHIEVED — but the reason is a DESIGN finding, not a wiring gap.** Verified independently: `emit_move` still has **ZERO callers** repo-wide (`grep -rn "\.emit_move(" src/` → no hits). Red-line probe (`val b = a; consume(a); print(a.x)`) runs clean, exit=0, no rejection. So use-after-move detection remains unreachable from ordinary code. **Root cause (from the new `mir_data.spl:337-353` docstring): Simple's surface language has no true move sites at all** — assignment is copy for structs and reference-share for classes, and `iso` parses but erases to `Infer` at HIR lowering. You cannot feed Move facts to the checker from a language that never moves. This is a **Category-3 design conflict**, not an unimplemented feature: matching Rust's use-after-move checking requires first deciding whether Simple gets move semantics at the surface — a user decision, not an implementation task. **What SF1 DID land (real, kept):** forward-propagated `moved_now` dataflow replacing the old same-point-only check, kill-on-reassign via new `record_assign`, a latent `Place.to_text()`/`BorrowKind.to_text()` crash fix, and native-Dict `.get()` pitfall avoidance. **26/26 specs green** across 4 files (8/7/8/3, all exit=0) — but those specs hand-build `Place`/`BorrowGraph` objects and never compile real `.spl` through MIR, which is exactly why they stayed green while the red-line probe failed. `emit_ref` has 2 pre-existing real callers plus 1 new one behind default-OFF `SIMPLE_BORROW_REF_CALL_ARGS=1`. Checker classes are all `class`, so the struct-accumulator landmine does not apply. **Good discipline:** the lane correctly identified that 3 of the 8 dirty files (`module_lowering`, `expr_dispatch`, `mir_lowering_stmts`) belong to OTHER concurrent lanes and excluded them. | orchestrator verify 2026-07-28 |
| SF2 `unsafe-boundary` | **ACCEPTED — biggest finding of the campaign.** TWO structural defects, both orchestrator-verified in the live tree, not on report. (1) **`struct SafetyChecker` → `class`**: the check functions thread `self` through a deep recursive walk and append to `self.context.errors` at arbitrary depth (7 sites), but as a value-type `struct` every `self` was COPIED into each nested call, so every diagnostic appended below the top frame was silently discarded on return. **The entire safety pass never reported anything, on any rule, ever** — it was structurally dead, exactly the "exists but starved" pattern this campaign was built to find (`HirLowering` already uses `class` for the identical reason). (2) **Dead legacy lexer state**: `parser_stmts.spl:495-518` detected `unsafe:`/`danger:` via `lex_peek_at()`, which reads the `lex_state_get("pos")` slot that `CoreLexer.next_token()` never writes back to — permanently stale, so the lookahead never saw the `:` and **`unsafe:` blocks were never recognized at all**. Same dead-slot bug also broke the raw `asm { ... }` scanner (spurious "unterminated asm block" on `asm { nop }`); fixed with new live accessors. **Scope check (orchestrator):** `lexer_scanners.spl` has ~10 more `lex_pos_get()` callers but is the self-consistent LEGACY free-function path — the defect only bites where `CoreLexer` and the legacy slot MIX, which is precisely the two sites SF2 fixed. Two parallel position states coexisting is a standing hazard worth a later unification. `parser_unsafe_block_spec` 3/3. `safety_checker_unsafe_boundary_spec` 3/5 — the 2 remaining failures are the documented `run_vs_test_harness_divergence_2026-07-28` class (interpreter drops one of two module-level fns when a module mixes `extern fn` with `fn`; `bin/simple run` confirms `functions.len()=2`), NOT introduced by this lane. | orchestrator review 2026-07-28 |
| SF3 `mir-interp-oob` | **done, VERIFIED GREEN** — `mir_interpreter.spl` +30/-11 loud OOB trap; official runner `mir_interp_bounds_check_spec.spl`: **6/6 passed** | small-agent verify 2026-07-28 |
| SF4 `mutex-guard` | **REVIEW-FLAGGED, not accepted** — closure-based `with_lock`/`with_read` landed (correct choice: defer/with dropped in interpreter, bug #172; closure identical on both engines); async mutex = documented sync-backed stub + filed bug `async_mutex_blocks_carrier_thread_no_suspend_2026-07-28.md`; lint PASS. **Blockers (revised 2026-07-28):** ~~(1) `rwlock_with_write` manual lock/unlock leaks on panic~~ — **ORCHESTRATOR RETRACTION: this blocker was WRONG.** Simple has no unwinding: no `try`/`catch`/`throw` by design (`.claude/rules/language.md`), and `rt_panic` → `spl_panic` → `exit(1)` (`src/runtime/runtime_legacy_core.c:340-343`, `runtime.c:1845`). A panic terminates the process, so an unreleased mutex is unreachable and the closure form is no safer than the manual pair. "Exception safety" is not a meaningful axis in this language; do not re-raise it against future guard lanes. (2) **ROOT CAUSE FOUND by orchestrator probe 2026-07-28 — REJECTED, needs redesign.** The guard signature `with_lock(f: fn(Any) -> Any)` is built on a broken primitive: **`Any`-typed closure parameters silently destroy the value.** Isolated 3-line probe: `fn(i64)->i64` param → `1` (correct); `fn(Any)->Any` param → **`nil`** (value gone); calling an `Any` closure directly → `<value:0x7>`, an undecoded tagged box. So EVERY `with_lock` call computes `updated = f(current)` = nil and then stores that nil back via `rt_mutex_unlock(handle, updated)` — **the guard destroys the protected data on every use, silently.** That is far worse than the hang it was blamed for, and plausibly causes it (a gate whose value became nil can leave the next acquirer spinning). Filed `any_typed_closure_param_destroys_value_2026-07-28.md`. **Fix direction, verified working:** use a generic parameter — `fn with_lock<T>(f: fn(T) -> T) -> T`; `apply_gen<T>` round-trips `42` and `"ok"` correctly. Re-do the lane on generics, not `Any`. Note this also retires the two agents' repeated "exception-safety gap" framing: that was never the problem. **(3) REDESIGN LANDED + ACCEPTED 2026-07-28.** All guards now generic: `Mutex.with_lock<T>(f: fn(T) -> T) -> T`, `RwLock.with_read<T>`/`with_write<T>`, plus free-fn forms. Orchestrator-verified: zero `fn(Any) -> Any` closure params remain (the one grep hit is a comment explaining the choice). **Write-gate solved properly:** the internal trampoline `mutex_with_lock_keeping<T>(mutex, keep_value: Any, f: fn() -> T)` takes a ZERO-ARG closure — the gate's stored value was never real data, so there was no reason to type-carry it through `T`; `keep_value` stays `Any` safely because it is always the fixed sentinel `0`, never user data. `f`'s result flows out untouched. **`Results: 19 total, 17 passed, 2 failed`, exit=1, no hang.** The 2 failures are a SEPARATE pre-existing defect, orchestrator-confirmed verbatim in Rust source: `interpreter_extern/atomic.rs:503-506` `Value::Str(s) => { // For now, convert string to NIL }` — so the default `PureStd` concurrent backend nulls EVERY text value, reproducible with a plain unguarded `mutex_lock` and zero guard code. i64/f64/bool round-trip correctly. Filed `mutex_rwlock_text_value_nulled_by_pure_std_backend_2026-07-28.md`. **Spec deliberately left RED** rather than skipped — per `.claude/rules/testing.md` failing tests are not skipped without approval, and a red spec keeps a real data-loss defect visible. Fix direction (`rt_set_concurrent_backend("native")` round-trips text) verified but NOT wired: flipping a process-wide backend from a leaf lib/spec is out of scope. | orchestrator review 2026-07-28 |
| SF5 `generation-handles` | **done, VERIFIED GREEN** — NVMe arena stamps real generations (`raw_nvme_arena.spl:90,98,122,130` bump-on-register/re-provision); specs green: generation 3/3, object_pool 12/12, resource_pool 17/17, thread_pool 4/4; lint 0 errors; 1 pre-existing unrelated failure (protocol_handler ServerHello echo — parallel session's db/server files) | small-agent verify 2026-07-28 |
| SF6 `doc-truth` | **done** — all 6 docs corrected: rust_migration mapping (4 falsehoods incl. E0805 → Add-to-Plan), memory_model_implementation status → "⚠️ PARTIAL" w/ evidence, MEMORY_VERIFICATION_COMPLETE append-only dated correction, capability_system/effect_system/extern_functions superseded-direction notes linking MC profile + audit. Non-MC behavior kept documented | agent report 2026-07-28 |
| R `const-ref-default` | **done, official runs blocked-on-runner** — new `const_ref_default.spl` (277L, text-level w/ `ponytail:` upgrade path = HIR effect analysis) + registration in `lint_checks.spl`/`config_and_model.spl` (warn ALL tiers, deliberately NOT in Reliable strict list); 14-example spec; direct-driver 14/14 PASS ×2 (interpreter engine; JIT deferred on cross-module symbol — known limit). UPDATE: real spec executed via direct driver — **14 examples, 0 failures**; lint 0 errors on all compiler files. Side-find to file: lint-CLI PARSE001 false-reject on valid spec syntax (pre-existing; sibling raw_rt_access_spec.spl also affected while executing green under the real parser) | agent report 2026-07-28 |
| N follow-up | `newtype`→`newunit` typo fixed inline by orchestrator (`primitive_classification.spl:86`); N spec running bg | — |
| R2 `bare-primitive-internal` | **landed, spec blocked-on-compile-time** — 20 files; mission-critical profile skeleton confirmed (`config_and_model.spl:59-60,156,178-184`); digit-separator lexer-parity (`1_000` bare vs `1_s` suffix, `bare_primitive_internal.spl:122-133`); lint exit 0; spec re-verify in consolidated pass | small-agent verify 2026-07-28 |
| DS1 `span-truth` | **ACCEPTED after orchestrator repair** — `merge()` now preserves `self.file` and computes `length`. Two agent claims were FALSE and had to be corrected: (a) "no Span.merge callers exist, fix is safe" — there are **6** live call sites in `src/compiler/30.types/dim_constraints.spl` (`e1.span.merge(e2.span)`, imports the same `compiler.common.diagnostics.span.Span`), so the fix is load-bearing, not cosmetic; (b) "spec passes linting" was offered as spec evidence, but the spec used `use std.test` + bare `fn test_*` and **never ran** (`Cannot resolve module: std.test`, `no examples executed`) — the known lint-doesn't-catch-unresolvable-imports landmine. Orchestrator rewrote the spec in the real `std.spec` DSL and extended the fix to `Span.new` + `Span.to`, which had the same hardcoded `length: 0`; `error_formatter.spl:409` sizes the caret underline from `span.length`, so every diagnostic underline was collapsing to 1 char. **7/7 passed, exit=0.** | orchestrator review + repair 2026-07-28 |
| DS3 `dwarf-wire` | **ACCEPTED with a scope caveat** — dead `emit_debug_info_header`/`emit_di_subprogram` wired end-to-end through the genuinely-reachable path (`MirToLlvm`, not just `LlvmBackend.compile_module`); `--debug-info=none\|line-tables\|full` CLI flag + `SIMPLE_DEBUG_INFO_LEVEL`. Gate = real LLVM 18.1.8 `llvm-dwarfdump` showing `DW_TAG_compile_unit` + `DW_TAG_subprogram`, then linked against a C driver and executed (returned 7). Two genuine pre-existing bugs fixed en route: (a) `emit_di_subprogram` allocated 3 **unreserved** metadata ids per call, corrupting numbering from the 2nd function on — now shares one `DISubroutineType`; (b) `!llvm.dbg.cu = !{!0}` rendered as `!llvm.dbg.cu = !true`. **Orchestrator verified (b) empirically** rather than on report: `{!0}` IS silently evaluated (`!0`→`true`) while `{!1, !2}` survives only because the comma makes it an invalid expression — so literal-brace safety is an accident of the grammar. Filed `string_interpolation_silently_evaluates_literal_braces_2026-07-28.md`; repo-wide scan shows 0 remaining instances, so DS3's fix was complete (my suspicion that sibling line 513 was also broken was WRONG). **CAVEAT — the CLI flag is NOT end-to-end verified:** `bin/simple` is currently the Rust SEED (`--version` prints the seed banner), whose own LLVM backend has no DWARF, so `compile --debug-info=full --emit-llvm` emits an `.ll` with zero `DISubprogram` regardless of these `.spl` changes. DS3's evidence via the interpreter path is valid for what it claims; the user-facing flag stays unproven until a bootstrap redeploy. Also unwired by design: WASM path, `compile_targets.spl` older native CLI, per-instruction `!dbg` (DS5). | orchestrator review 2026-07-28 |
| DS4 `log-dispatch` | **ACTIVE** (sonnet) — text→ring dispatch defect | — |

## Known Landmines (inherited, apply to all lanes)
- Native `Dict.get()` on struct values corrupt on HIT; `Dict.len()` always -1 — use
  `contains_key` + index reads / `keys().len()` (see CLAUDE.md Native-Codegen Dict Pitfalls).
- Neither JIT nor interpreter individually trustworthy — A/B when results look wrong.
- `simple test` child resolves `SIMPLE_BINARY` env else falls back to `bin/simple`
  (may be stale seed) — attribute evidence accordingly.
- Struct-name collision across modules in interpreter global registry — per-copy specs.

## Phase Checklist
- [x] 1-dev (goal registered)
- [x] 2-research (4 verification agents; §13 appendix)
- [x] 3-arch (wave/lane plan doc)
- [ ] 4-spec (each Batch-1 lane lands its spec with the change)
- [ ] 5-implement (Batch 1 lanes ACTIVE)
- [ ] 6-refactor
- [ ] 7-verify (orchestrator re-runs lint/tests per lane, then commits)
- [ ] 8-ship
