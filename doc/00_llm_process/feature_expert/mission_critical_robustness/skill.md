# Feature Expert: Mission-Critical Robustness (Simple vs Rust)

## Role

Own the process knowledge for the mission-critical robustness campaign: making Simple's
robust/mission-critical profile mechanically enforced and evidence-backed so its safety
claims meet or exceed Rust's for a declared certified subset.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Research (plan + verified audit): `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`
  — §13 = repo-verified ground truth (file:line) for every audit claim.
- Research (safety-property parity): `doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`
  — 15-row verification matrix, 4-category classification (spec'd-unimplemented /
  not-on-spec / conflicts / Rust-better-elsewhere), gap list G1-G10.
- Requirements: `doc/02_requirements/language/mission_critical_profile.md`
- Plan (waves + lanes): `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`
  — Batch 1 (truth foundations) + Batch 2 (safety-property enforcement SF1-SF6).
- SPipe state: `.spipe/mission_critical_harden/state.md` — live lane ledger, AC-1..AC-7.

## Key decisions (user-made)

- **Profile ladder rename (2026-07-28):** moderate (unchanged), strict (formerly lib), robust (formerly reliable), critical (formerly mission-critical). Old names are deprecated aliases (warn once). See `doc/02_requirements/language/mission_critical_profile.md` § Profile ladder rename.
- **Engine axis + default pairing (2026-07-28):** interpreter is the DEFAULT engine for run/test (dev loop); compiler/loader (native build) defaults to robust at WARN severity during migration. Interpreter/JIT→moderate; compiler/loader→robust-at-warn; `--profile` CLI flag or `simple.sdn [lints] profile=` override per-package. Bare `bin/simple run` = interpreter+moderate.
- Const-by-default references in MC mode: WARN now (`W-MC-REF-001`, landed), deny at
  critical profile v2. `mut` params + `me` receivers are the mutation opt-ins.
- Short borrowing range is a DESIGN DECISION, not a gap — never "fix" toward Rust.
- Unsafe: keep `unsafe:` blocks; replace blanket-allow with capability-scoped
  `@unsafe(reason, capabilities:[...])` + manifest in critical profile.
- Class-param mutation-by-design (s19 fix) is NOT reverted; enforcement layers on top.
- **PE profile-aware execution (REQ-MC-012):** `run`/`test` accept `--profile=moderate|strict|robust|critical` flag; profile gates lint levels + runtime check strictness. Deferred to Batch 3.
- **PR2 profile-rename-and-defaults lane:** implement deprecated aliases; compiler/loader robust-at-warn phasing. Queues behind R2; same config file.

## Affected layers / layer experts

- 35.semantics (lint: primitive table, semantic_api checker, const_ref, safety_checker)
- 50.mir + 55.borrow (SF1 borrow-feed) — see [mir_lowering](../../layer_expert/mir_lowering/skill.md)
- 95.interp (SF3 OOB trap)
- 70.backend (CUDA layout, Lean backend) — see [backend](../../layer_expert/backend/skill.md)
- stdlib concurrent/ + engine/resource/ (SF4 guards, SF5 generation handles)

## Implementation constraints

- Agents work disjoint file ownership; orchestrator commits; no agent self-declares done.
- Reproduce-first red specs for defect fixes; A/B both engines (neither individually
  trustworthy — see memory `reference_neither_engine_trustworthy_2026-07-27`).
- Native Dict.get() struct-payload corrupt + Dict.len()=-1: contains_key + index reads.
- Test runner contends under parallel sessions: foreground timeout 590s, direct-driver
  (`bin/simple run`) fallback, record blocked-on-runner explicitly.

## Verification commands

```bash
bin/simple test test/01_unit/compiler/lint/primitive_types_parity_spec.spl
bin/simple test test/01_unit/compiler/lint/const_ref_default_spec.spl
bin/simple test test/01_unit/compiler/types/units_newunit_registry_spec.spl
bin/simple test test/01_unit/compiler/semantics/symbol_id_spec.spl
bin/simple test test/00_formal_verification/compiler/tool_checker_spec.spl
```

## Handoff notes (2026-07-28, end of push wave)

**Everything below is PUSHED to origin/main and content-verified on the remote**
(6+ fast-forward pushes; commits e0bbe7daa10, 7938ce048b7, f07011139db1,
b51dd1c99ce6 among them). Full lane-by-lane evidence:
`.spipe/mission_critical_harden/state.md` ledger.

Landed: Batch 1 (P/N/G/S/B1/R/R2/A1); Batch 2 highlights — SF2 found the
campaign's two headline defects (`SafetyChecker` was a `struct` so every
recursive diagnostic was silently discarded — the pass NEVER reported anything;
`unsafe:` blocks never parsed due to a dead legacy lexer slot); SF4 redone on
generics after `fn(Any) -> Any` closure params proved to return nil (guard was
destroying mutex data every call); SF1 landed dataflow but its GOAL is blocked
on a design decision (below). Debug spine: DS1 span truth, DS2 DiagnosticV1,
DS3 DWARF wiring (real llvm-dwarfdump gate), DS5 MIR instruction spans, HS1
`HirFunction.span` population (the one hole DS1/DS3/DS5/DS2 all dead-ended at),
DS4 log text-dispatch. PR2 profile ladder rename (strict/robust/critical +
warn-once aliases) + docs. SE1: safety pass now ENFORCES at profile-gated
severity (`SIMPLE_SAFETY_PROFILE`: robust→ctx.add_warning, critical→
ctx.add_error; default advisory unchanged).

**Open — needs USER decision (do not implement without it):**
1. Move semantics: `emit_move` has zero callers BY DESIGN — Simple has no
   surface move sites (struct assign=copy, class=share, `iso` erased to Infer).
   Options + recommendation (make `iso` real) in
   `doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`
   § C3-NEW.
2. Another session's `feat(ui)` conflict root (5ff78c368048) — local only,
   never resolve it from this campaign's sessions.

**Batch D COMPLETE (2026-07-29):** DS1-DS8 all pushed. SE1+SE2 landed — the
safety pass ENFORCES and all three rules fire (SE2b found the third
silent-pattern-acceptance dead-code defect: `check_stmt` matched nonexistent
variants `Val`/`Var`/`AssignOp`, so every val/var initializer went unwalked).
DS6: real subprocess-pipe GDB MI transport + token table + lossless
breakpoints (seed lacks `rt_process_spawn_piped` — system spec skips honestly,
filed). DS7: CrashBundleV1 honest subset (signal-context extern gap filed with
exact rt_* signatures, not stubbed). DS8: OTLP JSON exporter + ObserveContext
(task/actor ids as plain i64 — real types live a tier up; wiring into std.log
+ scheduler is the named follow-up). Also RT1: a concurrent session's
monitor-timeout WIP broke EVERY `simple test` (`to_int("")` + interpreter
evaluates both sides of `and`) — fixed forward at all 4 sites.

**Next:** Batch 3 (G2 E1047, G7 iterators, G8 Transfer/Share, G9 cancellation,
Miri-mode, editions, SBOM); ObserveContext wiring; signal-capture externs
(runtime work); PE engine-flag lane.

**New landmines filed today (read before touching these areas):**
- `interp_lint_main_then_frontend_dict_to_int_2026-07-28.md` — executing
  lint-main's graph then `parse_full_frontend` in ONE interpreter session
  fails "cannot convert dict to int"; import alone is harmless. Never import
  `compiler.tools.lint.main` from driver-layer code or frontend-driving specs.
- `any_typed_closure_param_destroys_value_2026-07-28.md` — `fn(Any)->Any`
  params return nil; use generics `<T>`.
- `string_interpolation_silently_evaluates_literal_braces_2026-07-28.md` —
  `"{!0}"` renders `!true`; escape `{{ }}` or build braces via char codes.
- `hir_symbol_table_only_records_first_function_2026-07-28.md` — tooling-only
  (runtime fine); breaks md-links/LSP lanes until fixed.
- Stale-WC hazard is ACUTE: five separate disk files were behind origin in one
  day (mir_lowering_stmts, declaration_lowering, driver.spl −223 lines,
  driver_types, log.spl reverted twice). ALWAYS diff against fresh origin and
  run the me/fn symbol-loss guard before committing; commit via temp
  `GIT_INDEX_FILE` reland when `.git/index.lock` is contested.
