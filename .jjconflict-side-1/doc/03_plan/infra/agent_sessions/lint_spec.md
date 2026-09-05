# Lane: lint-spec — mission-critical robustness (ex-claude 79b2040e)

Goal (verbatim opening directive): "save next and update research doc. and make
pherallel agents dev plan. first make shared parts and agents to work
individually. **simple lsp and lint tool and refactoring tool should handle .md
link to simple.** research more how solve it. and find additional robust feature
needed and research paper often wrong and to impl existing feature. check them.
do more research with agent teams." — followed by the **Simple Mission-Critical
Profile** plan (7 measurable claims, 5 named blockers). Session Stop-hook goal:
"spipe dev skill, harden simple with the parallel simple harden plan."

Committed structure: Wave 0 contract-lock → lane **A** (primitive/enum), lane
**B** (md-link: B2 resolver, B3 md lint/fixer, B4 doc renderer, B5 LSP+rename),
lane **C** (Lean), lane **D** (ISA/GPU), lane **E** (Rust assurance ledger).

Plan docs (all on `origin/main`):
`doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`,
`.../simple_vs_rust_safety_property_audit_2026-07-28.md`,
`.../simple_vs_rust_debug_logging_2026-07-28.md`,
`doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`,
`doc/02_requirements/language/mission_critical_profile.md`,
`.spipe/mission_critical_harden/state.md`.

## Plan audit 2026-08-01

Evidence hygiene is best-in-class: **89 of 89** commit shas claimed in the
transcript are ancestors of `origin/main` — zero fabricated, zero unlanded.
Batch 1-2.5 genuinely landed: `35.semantics/lint/primitive_types.spl` (AC-1),
`30.types/units/unit_registry.spl` newunit collection (AC-2),
`90.tools/verify/checker.spl:351 _count_sorry` (AC-4),
`35.semantics/symbol_id/{stable_id,index,__init__}.spl` (AC-5),
`35.semantics/lint/semantic_api/checker.spl` (A1), and real enum payload
metadata (`parser_decls_types.spl:76-80`, `variant_payload_types_flat`).

**But the session declared the goal met while 4 of its 5 planned lanes were
still deferred, then drifted off-goal** into collection-planner IR work and
ENOSPC repo-wipe recovery. Needs-follow-up. Actionable next steps, in order:

1. **Correct the overstated status.** `.spipe/mission_critical_harden/state.md:8`
   says "ALL ACCEPTANCE CRITERIA MET — AC-1..AC-11 landed and pushed", yet the
   same file leaves phases 4-spec, 5-implement, 6-refactor, 7-verify and 8-ship
   unchecked and carries 4 `ACTIVE`, 2 `OPEN`, and 1 `GOAL NOT ACHIEVED` (SF1)
   lane rows. Replace with "Batch 1-2.5 AC met; B/C/D-registry/E outstanding"
   and reconcile the checklist.
2. **Fix FAILOPEN1 first.** `bin/simple test` exits 0 on a nonexistent path — a
   live fail-open that invalidates every "spec green" claim in the ledger.
3. **Restart the B lane — the user's single most explicit ask, never done and
   never approved as dropped.** No `semantic_link` module, no
   `simple ast-link` / `simple doc check-links`, no `W-DOC-AST-001` rule, no
   `spl:` URI support (`src/app/llm_process_gen/main.spl:652 should_check_link`
   still only filters `#`/`http:`/`https:`), and `query_api.spl:494/510
   prepare_rename/rename` have zero `.md` handling, so rename cannot rewrite
   markdown. `state.md:172` parked B2-B5 under "Scope Exclusions (Batch 1)…
   scheduled in later batches" and never revisited. SymbolId (AC-5) is landed,
   so B2's prerequisite is satisfied — this is unblocked today. Order: B2
   `std.tooling.semantic_link` → B3 `.md` walk in `_LintMain`/`lint_checks.spl`
   with `W-DOC-AST-001` → B5 `.md`-aware rename in `query_api.spl`.
4. **Lane C (Lean) C2-C5 is stubbed.** `70.backend/backend/lean_backend.spl`
   still has `export_types` = "# Would iterate through module type definitions"
   and `generate_proof_obligations` = "# Would analyze MIR...". The claim "zero
   admitted Lean proofs in the certified closure" is currently unenforceable.
5. **Lane E (Rust feature assurance ledger) does not exist** — no doc, no file;
   `ferrocene` appears only in the two research docs.
6. **Lane D ISA registry does not exist** — no `*isa*registry*` artifact, so
   "no silent scalar or unsupported-instruction fallback" is unenforced.
7. **Trust manifest / reproducible-artifact gate** is prose in the requirements
   doc only; nothing in `src/`.
8. **REQ-MC-012 (profile-aware execution)** — requirements doc line 121 says
   `Status: NOT IMPLEMENTED — Batch 3 lane`.
9. **Boundary manifests (A5, `@representation_boundary`)** are doc-only, zero
   `src/` hits.
10. Lanes left hanging at session end: SF1 (`GOAL NOT ACHIEVED`), VHDL2, DS4,
    G9b, HIR1, PTR1 (all `ACTIVE`).

Either land items 3-9 or get an explicit user de-scope on record — none of them
were de-scoped by the user.

## sspec sufficiency 2026-08-01

**Runner:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`;
the live `bin/simple` has no `test`/`run`/`lint`/`check` subcommands at all.
Falsifiability was proven on a scratch spec before any lane was run (wrong
numeric oracle and wrong text oracle both failed, exit 1). See `layout_web.md`
§"sspec sufficiency 2026-08-01" for the shared runner/harness evidence,
including the finding that `simple test` silently delegates execution to the
Rust seed at `src/compiler_rust/target/debug/simple`.

**Correction to item 2 above (FAILOPEN1).** On this runner `simple test` is
**not** fail-open: a nonexistent spec path exits **1** with
`error: test file not found: ...`. Either the defect was fixed before this
binary was cut, or the original observation was made against a different
binary. Re-confirm against whichever binary the ledger's "spec green" claims
were produced on before treating FAILOPEN1 as live — but it does not reproduce
here.

### Coverage verdict — no system-tier spec backs any claimed AC

Searching `test/03_system/` for the ACs' subject matter returns nothing that
actually tests them:
- `test/03_system/app/lint_cli_contract_spec.spl` is a real system spec for the
  lint CLI, but it contains **zero** references to `W-MC-*`, the primitive
  table, `newunit`, `SymbolId`, or the sorry gate — it covers generic CLI
  contract behaviour (exit codes, JSON Lines, directory expansion), not this
  lane's ACs.
- `test/03_system/feature/usage/primitive_types_spec.spl` is a **language
  feature** spec (enums, unions, type aliases, optionals, generics). Despite the
  name it has nothing to do with AC-1's "one canonical primitive table consumed
  by lint".

Every AC that has any executable coverage is covered **only at unit tier**:
AC-1 → `test/01_unit/compiler/lint/bare_primitive_internal_spec.spl` and
`const_ref_default_spec.spl` (the only three files repo-wide that mention
`W-MC-`, the third being `param_mutability_semantic_spec.spl`);
AC-2 → `test/01_unit/compiler/types/units_newunit_registry_spec.spl`;
AC-4 → `test/00_formal_verification/compiler/tool_checker_spec.spl`;
AC-5 → `test/01_unit/compiler/semantics/symbol_id_spec.spl`;
A1 → `test/01_unit/compiler/lint/semantic_api_checker_spec.spl`.
These specs `use` the real `.spl` modules under test, so they are genuine
evidence for the landed Batch-1/2.5 code — just not system-tier evidence.

Missing scenarios — no spec at any tier:
- **Lane B (md-link), the user's single most explicit ask.** `grep` for
  `semantic_link`, `W-DOC-AST-001`, or `ast-link` across `src/` **and** `test/`
  returns **zero files**. `src/compiler/90.tools/query_api.spl` contains **0**
  occurrences of `.md`, confirming `prepare_rename`/`rename` cannot rewrite
  markdown. There is nothing to test because nothing was built.
- **Lane C (Lean) C2-C5** — no spec for `export_types` /
  `generate_proof_obligations`; the "zero admitted Lean proofs" claim has no
  executable gate.
- **Lane D ISA registry** and **Lane E Rust assurance ledger** — no artifact, so
  no spec.
- **AC-3 (CUDA field offsets/GEP/cast)** — no spec ties any CUDA backend spec to
  the mission-critical layout claim.
- **Trust manifest / reproducible-artifact gate**, **REQ-MC-012 profile-aware
  execution**, and **A5 `@representation_boundary` boundary manifests** — all
  doc-only, zero `src/` hits, therefore zero coverage.

### Run results — NOT OBTAINED

The five AC-bearing specs plus the two mis-named system candidates were queued
but **produced no verdicts**. The batch was abandoned after the environment was
proven unusable: the 3-example scratch probe that completed in ~60 s at 04:00
**timed out at 400 s** when re-run at 04:26, and the preceding lane timed out
4 of 4 specs at 300 s each. Box load average climbed 13 → 18 → 42 → **101** on 32
cores under competing sibling-worktree bootstrap builds; even
`simple test --help` exceeded 120 s. See `l1_pair_b.md`
§"sspec sufficiency 2026-08-01" for the full control experiment.

Re-run on a quiet box before drawing conclusions. Note that the coverage verdict
below **does not depend on these counts**: the specs that exist only cover
AC-1/2/4/5 + A1 — the subset this audit already found genuinely landed — so no
amount of green could substantiate the state file's claim about B/C/D/E.

**Verdict: insufficient** (coverage), **cannot-run** (execution). The state
file's
`ALL ACCEPTANCE CRITERIA MET — AC-1..AC-11 landed and pushed` (line 8) is not
supportable by the test suite: phases 4-spec through 8-ship are unchecked in the
same file, there is **no system-tier spec for any AC**, and four of the five
planned lanes have neither implementation nor specs. Item 1 above (correct the
overstated status) should be treated as the blocking action.
