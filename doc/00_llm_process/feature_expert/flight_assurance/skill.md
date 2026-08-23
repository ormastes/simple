# Feature Expert — flight assurance (`critical` + `flight-core-v1` + `aero-a`/`space-a`)

## Role

Own the aerospace-hardening campaign's process knowledge: the canonical flight-rule
registry, the four frozen WP-0 schemas, and what is actually enforced versus merely
declared.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Research: [`doc/01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md`](../../../01_research/language/assurance/aerospace_grade_hardening_research_2026-08-07.md)
- Plan (authority): [`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`](../../../03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md)
- Cert roadmap: [`doc/03_plan/cert/cert_roadmap.md`](../../../03_plan/cert/cert_roadmap.md)
- Profile requirements: [`doc/02_requirements/language/mission_critical_profile.md`](../../../02_requirements/language/mission_critical_profile.md)
- Source: `src/compiler/00.common/assurance/`
- Specs: `test/01_unit/compiler/assurance/`

## Current state (WP-0 landed, 2026-08-07)

`src/compiler/00.common/assurance/` holds the canonical registry and the four frozen
schemas. `00.common` is the low-dependency layer — nothing here may import upward. That
constraint is *why* the registry lives here: `80.driver` could not import `90.tools`,
which is how the profile tables came to be duplicated
(`src/compiler/80.driver/driver_safety_severity.spl:4-22`).

| File | Contents |
|---|---|
| `flight_rules.spl` | `FlightRuleV1` + the `FLT-*` registry + `flight_rules_hash()` |
| `policy_schema.spl` | `ResolvedAssurancePolicyV1` + `policy_hash()` (schema only) |
| `symbol_summary.spl` | `CriticalSymbolSummaryV1` + its eight lattices |
| `stamp.spl` | `AssuranceStampV1` + `ExternProviderSummaryV1` |
| `docgen.spl` | Pure renderers: crosswalk, severity table, enforcement-gap report |

## Constraints a later WP must not rediscover

- **`analyzer: "none"` means two different things.** Discriminate with `critical_level`:
  `Intrinsic` = no analyzer is *needed* (the grammar cannot express the violation);
  anything else = a real unfilled gap. `FlightRuleV1.is_enforcement_gap()` encodes this,
  and WP-2's census must key off it.
- **Where a rule *is* enforced, `analyzer` names the twin that actually fires.** Per plan
  premises 12b/13 the live emitters are the TEXT reimplementations in
  `90.tools/lint/_LintMain/lint_checks.spl`, not the `35.semantics/lint/*` checkers.
  WP-7/WP-8 flip those two rows once the twin dies.
- **The three level fields are a grade ladder**, not a today→target roadmap, and the
  ladder is monotone. A spec enforces the monotonicity.
- **`sources` are as-cited, unverified.** Network fetch is blocked here; the renderers
  emit `source_verification_note()`.
- **No module-level `val` built from a function call** — reads zero under native codegen.
  `flight_rules()` rebuilds on every call on purpose.
- **No dict keyed to struct values** — `find_flight_rule` is a linear scan on purpose.
- **`if opt:` on an absent optional takes the PRESENT branch** (RT_NIL is sentinel 3).
  Use `.?` in condition position. Open defect:
  `doc/08_tracking/bug/bare_optional_in_condition_position_wrong_branch_2026-08-01.md`.

## Reachability (do not overclaim)

`bin/simple` is the Rust seed and stage-3 self-host is blocked, so a pass added under
`src/compiler/**` outside `90.tools/lint` enforces nothing for users yet. The deployed
lint binary also predates its own source (plan premise #0.2), so a `.spl` lint edit is
not observable until WP-3.5's redeploy. WP-0 is 🟢 only because it is data + docgen.

## Layer experts

- `00.common` — low-dependency compiler layer (this WP)
- `80.driver`, `90.tools/lint` — WP-3/WP-4/WP-7/WP-8 targets
- `35.semantics` — WP-6/WP-11/WP-12 targets

## Verification

```bash
bin/simple lint src/compiler/00.common/assurance/*.spl
bin/simple test test/01_unit/compiler/assurance/ --no-cache --no-cover-check
```

The only authoritative verdict is the final `^Results:` line; take `$?` from the command
itself, never from a pipe.

## Warning phase — the one-level severity downgrade (2026-08-23)

An assurance profile can be run in a **warning phase**: every diagnostic it
raises drops **exactly one** severity level. The migration ramp INTO
mission-critical — see what would fail before the build fails.

Selected by `SIMPLE_ASSURANCE_WARNING_PHASE=1`, `simple lint
--assurance-warning-phase`, or `warning_phase: true` in the `lints:` SDN
section. Truthy: `1 true yes on warn warning`; **anything else means full
severity** — the knob fails closed.

Three things to know before touching it:

1. **It is a MODIFIER, never a profile name.** A `critical:warn` suffix makes
   `normalize_profile_name` return `""` at any un-updated consumer, which
   resolves to moderate/Advisory — a suffix fails **open**. A separate knob
   fails **closed**. Do not "simplify" it into the (frozen) name table, and do
   not add a field to the (frozen) `ResolvedAssurancePolicyV1`.
2. **It is a severity transform, not a mute.** The downgrade clamps at the
   lowest rung that still REPORTS: Advisory for the driver (log-only via
   `SIMPLE_SAFETY_WARN`), **Warn** for lint (`Allow` is silence, so lint clamps
   one rung above its enum's bottom).
3. **The interpreter's bool projection is partial, deliberately.** Only
   `match_fallthrough_set_abort` is downgraded.
   `match_wildcard_catch_set_enabled` is a *visibility* flag and
   `import_admission_set_deny` is an *admission gate* — flipping either would
   make critical-under-warning-phase report LESS than critical. Both stay keyed
   to the raw profile; the admission gate carries a
   `TODO [interp][P2][warning-phase]` to grow a warn rung.

Source: `src/compiler/00.common/assurance/warning_phase.spl` (zero `use` lines,
zero module-level state — same constraint as `policy_names.spl`).
Guide: `doc/07_guide/compiler/assurance_warning_phase.md`.
Spec: `test/01_unit/compiler/assurance/assurance_warning_phase_spec.spl` (18/18).
