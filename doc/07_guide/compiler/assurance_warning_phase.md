# Assurance warning phase — the one-level severity downgrade

*Added 2026-08-23. Source of truth: `src/compiler/00.common/assurance/warning_phase.spl`.*

## What it is

An assurance profile — `mission-critical` especially — can be run in a
**warning phase**. Every diagnostic that profile would raise drops **exactly
one severity level**: what would be an error becomes a warning, and so on down
the ladder.

This exists so a codebase can be migrated **into** a stricter profile
incrementally. You turn on `critical`, run it in warning phase, and see
everything that *would* fail without the build failing.

It is **not** a "ignore errors" switch and **not** a way to silence anything.
Nothing becomes invisible: an error-turned-warning is still reported.

## Selecting it

| surface | spelling |
|---|---|
| environment | `SIMPLE_ASSURANCE_WARNING_PHASE=1` |
| CLI (`simple lint`) | `--assurance-warning-phase` |
| project SDN (`lints:` section) | `warning_phase: true` |

Accepted truthy values: `1`, `true`, `yes`, `on`, `warn`, `warning`
(case-insensitive). **Anything else — including a typo — means no downgrade,
i.e. full configured severity.** The knob fails closed.

The CLI flag writes the env knob, so one selection reaches all three
projections and two components cannot end up disagreeing about the phase.

## Why a modifier, not a profile name

`policy_names.spl` states its alias set is FROZEN, so `critical-warn` is out of
bounds by construction. But the decisive reason is **failure direction**:

* A name/suffix encoding (`SIMPLE_SAFETY_PROFILE=critical:warn`) makes
  `normalize_profile_name` return `""` at every consumer that was not updated,
  and `""` resolves to moderate/Advisory. A suffix therefore fails **open** —
  an un-updated projection silently enforces *less* than it does today.
* A separate knob fails **closed** — an un-updated consumer ignores the
  modifier and keeps enforcing **full** severity. Never weaker than today.

Mission-critical infrastructure takes the fail-closed encoding.

`ResolvedAssurancePolicyV1` is deliberately **not** touched: it is a frozen
schema, and the modifier is orthogonal to strictness anyway.

## The three projections, and what each can express

The five profile-name consumers keep three different projections of one table.
The downgrade lands differently in each, and the differences are real:

| projection | ladder | under warning phase | floor |
|---|---|---|---|
| driver `SafetyPassSeverity` | Deny / Warn / Advisory | Deny→Warn, Warn→Advisory | **Advisory** — log-only via `SIMPLE_SAFETY_WARN`, still reports |
| lint `LintLevel` | Deny / Warn / Allow | Deny→Warn, Warn→Warn | **Warn** — `Allow` is silence, so lint clamps one rung *above* its enum's bottom |
| interpreter `bool` | deny / not-deny | true→false (one step) | `false` |

### The interpreter's bool, stated honestly

A bool can encode exactly one step of the ladder — Deny→Warn — and nothing
below it. It cannot express Warn→Advisory, so `false` clamps.

More importantly, `eval_apply_assurance_profile` fans that one bool out to
three flags, and **only one of them is a severity**:

* `match_fallthrough_set_abort` — a real severity. `false` still emits the
  warn-only fall-through diagnostic. **This one is downgraded.**
* `match_wildcard_catch_set_enabled` — a **visibility** flag. `false` stops the
  wildcard diagnostic being emitted at all. Downgrading it would make
  critical-under-warning-phase report *less* than critical. **Not downgraded**;
  stays keyed to the raw profile.
* `import_admission_set_deny` — an **admission gate**. `false` silently admits
  the built-in-fallback import (`module_loader_core.spl:499`) with no
  diagnostic of any kind. It has no warn rung to fall to. **Not downgraded**;
  tracked by a `TODO [interp][P2][warning-phase]` to give it one.

Net: a `critical` interpreter session in warning phase stops **aborting** on
match fall-through while still reporting it, and reports strictly no less than
it did without the phase.

## API

```
compiler.common.assurance.warning_phase
    warning_phase_env_var_name() -> text
    warning_phase_flag_name() -> text
    warning_phase_enabled_for_value(raw: text) -> bool
    severity_rank_advisory() / severity_rank_warn() / severity_rank_deny() -> i64
    downgrade_severity_rank(rank, floor_rank) -> i64
    phased_severity_rank(rank, floor_rank, warning_phase) -> i64

compiler.driver.driver_safety_severity
    safety_pass_severity_downgraded(sev) -> SafetyPassSeverity
    safety_pass_severity_for_name_phased(raw, warning_phase) -> SafetyPassSeverity
    safety_pass_severity_for_strictness_phased(strictness, warning_phase)
    safety_pass_severity_for_policy_phased(policy, warning_phase)
    safety_pass_warning_phase() -> bool          # thin env wrapper
    safety_pass_severity_phased() -> SafetyPassSeverity

compiler.tools.lint.main
    downgrade_lint_level(level) -> LintLevel
    phased_lint_level(level, warning_phase) -> LintLevel
    LintConfig.set_warning_phase(on) / set_warning_phase_from_value(raw)

compiler.frontend.core.interpreter
    eval_apply_assurance_profile_phased(profile_name, warning_phase)
```

Names other than `warning_phase_env_var_name` / `warning_phase_flag_name` are
leaf-import only (`use compiler.common.assurance.warning_phase.{...}`) — they are
plain `fn`, not `pub`, because bare-primitive signatures trip `primitive_api`.

Every downgrade function is a **pure function of its arguments**; the
environment is read only in thin named wrappers, so specs never mutate the
process environment. `warning_phase.spl` carries zero `use` lines and zero
module-level state, the same constraint (and for the same interpreter-graph
reason) as its sibling `policy_names.spl`.

## Tests

`test/01_unit/compiler/assurance/assurance_warning_phase_spec.spl` — 18
examples. The load-bearing ones are *not* "a downgrade happens" (a blanket
set-everything-to-warn would satisfy that) but: exactly one rung; still
reported; unchanged when off across the whole canonical ladder; the bottom of
each ladder; and fail-closed spelling.

Discrimination evidence (mutation, not assertion-counting):

| mutation | result |
|---|---|
| `downgrade_severity_rank` returns `rank` instead of `rank - 1` | **7 of 18 fail** |
| lint's `_lint_level_of_rank` fallback returns `LintLevel.Allow` and the floor is lowered below Warn | **2 of 18 fail** |
| lint's floor lowered below Warn *only* | **survives** — see below |

The surviving mutation is recorded rather than hidden: lint's clamp is
**double-guarded**. The `Warn` floor and `_lint_level_of_rank`'s `fallback`
argument each independently prevent a downgrade reaching `Allow`, so lowering
the floor alone changes no observable behaviour. The property "lint never
downgrades into silence" *is* pinned — the third mutation, which defeats both
guards, is killed — but the floor constant on its own is redundant belt-and-
braces, not the sole mechanism.
