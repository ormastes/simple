# Independent review — mission-critical warning phase + alloc diagnostic config (2026-08-23)

Reviewer: independent (not a lane author). Worktree `/mnt/data/worktrees/mcreview-1`
@ `origin/main` = `97c68bcc3cd`. Commits under review: `97c68bcc3cd` (Feature 1),
`6c78a408f8d` (Feature 2), `763ce237974` (Wave 5 plan).

Binary used for every spec run below (identity recorded per `.claude/rules/commands.md`):
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
60,650,360 B, mtime 2026-08-23 04:47:05 UTC (the Rust seed). `SIMPLE_TIMEOUT_SECONDS=0`.

Measured, not taken on trust:
- `test/01_unit/compiler/assurance/assurance_warning_phase_spec.spl` — `outcome=OK executed=18 passed=18 failed=0`.
- `test/01_unit/compiler/semantics/mission_critical_alloc_config_spec.spl` — `outcome=OK executed=7 passed=7 failed=0`.

## Overall judgement

The design is sound, the discipline claims hold, and the code is correct where it
runs. **One claim is materially overclaimed: "All three projections handled."**
The driver projection is written but **not wired** — `safety_pass_severity_phased()`
has zero production call sites. Feature 2 is entirely latent by its own admission.

Verdict: **proceed to M1, but M1's first action must be the driver wiring**, and the
M0 "feature freeze / both lanes' specs green" row must not be read as "the driver is
in warning phase". Nothing found here blocks M2/M3 beyond their own dependencies.

## Per-claim verdicts

**Claim 1 — one level, never silenced. VERIFIED for the logic; PARTIALLY WIRED.**
- Driver: `driver_safety_severity.spl:117-135`. Rank round-trip is correct;
  `_safety_severity_of_rank` floors at `Advisory`, and `safety_pass_severity_for_name`
  (`:60-77`) makes `Advisory` the same rung an unset profile already gets, i.e. the
  existing log-only `SIMPLE_SAFETY_WARN` path. Legitimate reporting floor.
- Lint: `config_and_model.spl:369-393`. `Deny(2)→Warn(1)`; `Warn(1)` hits
  `rank <= floor` and is returned unchanged; `Allow` (rank 0) returns the `fallback`
  argument, i.e. itself. No path reaches `Allow` from a reporting level. Applied at
  all three `get_level` returns (`:536,541,543`).
- Interpreter: `eval_decls.spl:349-352`, `abort = deny and not warning_phase`.
  Verified the diagnostic survives: `report_match_fallthrough(...)` is called
  **unconditionally** at `eval_stmts.spl:691` and `eval.spl:916`, *before* the
  `match_fallthrough_get_abort()` check. Downgrade = report-without-abort. Correct.

**Claim 2 — suffix fails open, separate knob fails closed. VERIFIED in source.**
`policy_names.spl:55-65`: any unrecognised spelling (`critical:warn` included)
returns `""`. `driver_safety_severity.spl:60-77`: `""` falls through to
`SafetyPassSeverity.Advisory` — strictly weaker than the `Deny` it replaced. A
separate knob is ignored by an un-updated consumer, leaving full severity. The
load-bearing design argument is real, not rhetorical.

**Claim 3 — partial interpreter fan-out. Reasoning SOUND; TODO adequate; the
fail-open is PRE-EXISTING, not introduced.** Read `module_loader_core.spl:495-508`
directly: with `_import_admission_deny` false, the built-in-fallback branch calls
`module_mark_loaded(module_name, "", imported_names); return 1` with **no diagnostic
of any kind**. Downgrading that flag would therefore make critical+phase report less
than critical — exactly what the feature forbids — so excluding it is right. Same for
`match_wildcard_catch_set_enabled` (visibility, not severity). The
`TODO [interp][P2][warning-phase]` at `eval_decls.spl:341-343` names the right fix
(give admission a warn rung). Note the silent-admit hole predates this commit and is
not a regression from it.

**Claim 4 — lint mutation weakness. HONEST, and the property is genuinely pinned.**
The lane's own note is accurate and, if anything, understates the reason. Lowering the
floor from `severity_rank_warn()` to `severity_rank_advisory()` still yields
`Warn→Warn`, because `_lint_level_of_rank(0, fallback)` returns the *original* level
rather than `Allow` (`config_and_model.spl:381-387`). Two independent mechanisms
enforce "never reaches Allow". So the property is pinned twice and the constant alone
is not the sole mechanism — the correct reading. The spec's
`downgrade_lint_level(LintLevel.Warn) != LintLevel.Allow` assertion is the negative
control and it is present (`spec:126-128`).

**Claim 5 — fail-closed parse. VERIFIED.** `alloc_diagnostic_config.spl:91-107`:
empty raw → empty config; entry with no `=` → dropped; empty scope or empty
justification → dropped. `mc_alloc_allowance_for:77-81` additionally re-checks
`a.justification != ""`, so even a hand-constructed unjustified allowance grants
nothing. `mc_alloc_scope_matches:68-71` returns false for `scope == ""`. Default
`McAllocDiagnosticConfig.default()` is empty and `check_steady_state_gate`
(`noalloc_checker.spl:358+`) delegates with it — byte-identical to the pre-config gate.

**Claim 6 — exact-or-dot-boundary. VERIFIED and PINNED.**
`symbol == scope or symbol.starts_with(scope + ".")` (`:71`), and the regression is
pinned by a real negative case: `mission_critical_alloc_config_spec.spl:87-91`
asserts `mc_alloc_scope_matches("boot_init", "boot_init_unsafe") == false`. A revert
to bare `starts_with` fails that example.

**Claim 7 — check never deleted. VERIFIED, with a caveat.**
`steady_state_findings` produces a finding for *every* non-steady-state-safe symbol
and tags it `allowed` + `justification`; `format_steady_state_finding` renders
`allowed[steady-state]: ... permitted by ...: <why>`. Caveat: the reporting machinery
also has zero production callers, so "still reported" is true of the API, not yet of
any user-visible output.

**Claim 8 — latency. CONFIRMED; the feature is CURRENTLY DECORATIVE.**
`SIMPLE_MC_ALLOC_ALLOW` is read nowhere: it appears only in this module's own header
comment and in the spec. `check_steady_state_gate_with_config` /
`steady_state_findings` / `format_steady_state_finding` have no caller outside
`35.semantics/__init__.spl`'s re-export and the specs. The gate it configures was
already latent (the plan's §27 row says so). It is a well-built, correct, fail-closed
API that nothing yet calls — load-bearing only once M2 wires it. Stated plainly: as
landed, it changes zero compiler behaviour.

**Claim 9 — `policy_names.spl` discipline. VERIFIED for both features.**
`warning_phase.spl` and `alloc_diagnostic_config.spl` each have **0** `use` lines and
**0** module-level `var`/`val` (grep-verified). Both sit in `00.common`; importers are
`80.driver`, `10.frontend`, `90.tools`, `35.semantics`, `src/app/io` — all
higher-numbered, so layering is respected and neither imports `90.tools`. The frozen
alias set in `policy_names.spl` is untouched by both commits; no
`ResolvedAssurancePolicyV1` field was added.

**Claim 10 — shared-hunk ordering. The premise is FALSE; no conflict exists.**
`comm -12` over the two commits' file lists yields exactly one shared path:
`doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`. Neither
commit touches `assurance/__init__.spl` and `config_and_model.spl` jointly — Feature 2
touches neither. Both plan-doc hunks are `1 insertion, 0 deletions` and both rows are
present at HEAD (`:2511` warning phase, `:2688` alloc config). They composed cleanly
because they never overlapped.

**Claim 11 — do the specs discriminate? PARTLY.**
- Genuinely discriminating: the lint `Warn ≠ Allow` control, the fail-closed value
  table (`spec:150-152`, 8 negative spellings), the identity-when-off assertions over
  the whole ladder, and the alloc sibling-prefix negative. These fail on a real
  mutation of the code under test.
- Weak: `outcome=ERROR executed=0` pre-feature evidence proves only that the spec
  cannot *resolve* without the new module. It cannot distinguish a correct
  implementation from a wrong one — any module exporting those names would clear it.
  Confidence bought: "the code is reached", not "the code is right". The mutation
  results the lane reported (7/18 and 2/18 killed) are the real discrimination
  evidence and are worth more than the revert evidence.
- **Gap:** the interpreter projection has **no test at all**. `@cover` in
  `assurance_warning_phase_spec.spl:1-4` lists `warning_phase.spl`,
  `driver_safety_severity.spl`, `config_and_model.spl` — not `eval_decls.spl`, and no
  example exercises `eval_apply_assurance_profile_phased`. Of the three projections
  the commit claims, one is unwired and one is untested.

**Claim 12 — Wave 5 gate design. SOUND, and it would honestly FAIL today.**
The `N=0 downgraded diagnostics = FAIL` rule in M1 (`mission_critical_infra_hardening_v2.md`,
M1 row) is exactly the right shape and, given defect D1 below, the M1 gate would report
N=0 and FAIL on the current tree. That is the gate working as designed, and it is the
strongest evidence in this review that the plan's gates discriminate. The M0
"downgrade-is-reported negative control (a silenced diagnostic FAILS the spec)" is
already satisfied in miniature by the lint `!= Allow` assertion. Two residual gaps in
the plan: no M-row requires the interpreter projection to have a test, and no row
requires the alloc config to acquire a production caller before M2's gate can be
non-vacuous (R-W6-adjacent; the plan's premise-7 note gestures at it but does not gate on it).

## Defects, ranked

**D1 (major, overclaim) — the driver projection is dead code.**
`safety_pass_severity_phased()` (`driver_safety_severity.spl:167`) has zero production
call sites. The two real driver consumers still call the unphased
`safety_pass_severity()`: `driver_hir_pipeline_lowering.spl:1032` and
`driver_hir_pipeline_passes.spl:243`. Setting `SIMPLE_ASSURANCE_WARNING_PHASE=1`
therefore changes lint and the interpreter but leaves every driver safety pass at full
severity. The commit message's "All three projections handled" is an overclaim; the
accurate statement is "logic written for three, wired for two". Not fixed here — M1 is
the sanctioned wiring step, and a reviewer should not land the wiring.

**D2 (minor) — three functions with no caller at all.**
`safety_pass_severity_for_strictness_phased` (`:150`) and
`safety_pass_severity_for_policy_phased` (`:157`) are unreferenced by product code
*and* by the spec. `.claude/rules/code-style.md` says never add unused code. They are
plausibly M1's intended entry points, so the right disposition is to use them in M1 or
delete them, not to leave them indefinitely.

**D3 (minor) — untested interpreter projection.** See claim 11. One example asserting
`eval_apply_assurance_profile_phased("critical", true)` leaves
`match_fallthrough_get_abort() == false` while `("critical", false)` leaves it `true`
would close it; `policy_five_site_convergence_spec.spl:213-227` already imports the
getter, so the harness exists.

**D4 (cosmetic) — header overclaim in `warning_phase.spl:52-54`.** "the ONE
environment read lives in a thin named wrapper" reads as if that wrapper is in this
file. There is no env access in `warning_phase.spl` at all; the wrappers are in the
three consumers. The discipline claim is true, the sentence's location is misleading.

**D5 (watch item, not a defect) — non-hermetic `LintConfig.new()`.**
`config_and_model.spl:415-421` reads the env in the constructor. Correct for the
"one knob reaches all projections" goal, but it means every `LintConfig` built in any
process inherits ambient phase. The specs override explicitly so they are safe; a
future spec that does not could pass or fail based on the ambient environment.

## Recommendation

Proceed to **M1**, with the wiring of `safety_pass_severity_phased()` into
`driver_hir_pipeline_passes.spl:243` and `driver_hir_pipeline_lowering.spl:1032` named
as M1's first action and its gate's `N>0` assertion treated as the proof it landed.
**M2** may proceed but its gate is vacuous until something reads
`SIMPLE_MC_ALLOC_ALLOW`; make that a precondition, not a deliverable.
**M3** should carry D3's missing test. D2 and D4 are cleanup, not blockers.
Nothing here justifies reverting either commit.
