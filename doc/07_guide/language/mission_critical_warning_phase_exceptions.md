# Allocatable mission-critical mode: warning phase + exceptions (step 1)

**Added 2026-08-28.** Config keys live under `lints:` in the package
`simple.sdn` (`src/compiler/simple.sdn`, `src/lib/simple.sdn`). Readers:
`src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
(`LintConfig.from_sdn_string`) and the exception leaf
`src/compiler/00.common/assurance/mc_exceptions.spl`.

## What "allocatable mission-critical" is

`critical` is the canonical name of the mission-critical assurance profile
(`compiler.common.assurance.policy_names`; `mission-critical` /
`mission_critical` are frozen deprecated aliases). It is **robust + REQ-MC
rules** (`config_and_model.profile_default_levels`, case `Critical`), and on
the compile driver it makes the safety pass **deny**
(`80.driver/driver_safety_severity.spl:59-75`).

"Allocatable" means the profile does **not** demand `@noalloc`: allocation is
permitted. The only allocation gate the tree has is the WP-12 steady-state
gate in `35.semantics/noalloc_checker.spl`, which is (a) not wired as a build
gate and (b) configured by
`00.common/mission_critical/alloc_diagnostic_config.spl`, whose
`mc_alloc_toolchain_allowances()` admits the `compiler.*` namespace (compiler,
loader, interpreter) with a recorded justification. `src/lib/nogc_async_mut_noalloc`
keeps its `@noalloc` guarantee — that is a per-function annotation, not the
profile.

## The three keys

```sdn
lints:
  profile: critical
  warning_phase: true
  mc_exceptions: "src/lib/skia=vendored bindings, src/lib/gc_sync_mut=outside step-1 scope"
```

| key | effect | enforced at |
|---|---|---|
| `profile: critical` | selects the tier (robust denies + `bare_primitive_internal`/`unwrapped_foreign_resource` at warn) | `config_and_model.spl` `profile_default_levels` |
| `warning_phase: true` | every level the tier yields drops EXACTLY ONE rung: deny -> warn; warn stays warn (lint floor is Warn, never Allow) | `config_and_model.spl` `phased_lint_level`; driver: `driver_safety_severity.safety_pass_severity_phased` via `SIMPLE_ASSURANCE_WARNING_PHASE=1` |
| `mc_exceptions` | files inside a listed scope are linted at `strict` instead of `critical`, and the skip is REPORTED with its reason | `entry_and_fixes.spl` `_run_lint_with_linter_source` |

Precedence is unchanged: `--profile=` CLI > `simple.sdn` > engine default;
a file-level `@lint_profile(...)` still wins over all of them. An exception
only ever applies when the resolved tier IS critical — it can never raise a
weaker profile.

## Exception grammar

`scope=reason` entries separated by `,`. `scope` is a **repo-relative path
prefix** (directory or single file) matched on a `/` boundary, so
`src/lib/gc` does not cover `src/lib/gc_sync_mut`. A leading `./` and a
trailing `/` are ignored. The reason is mandatory; an entry with an empty
scope or reason is dropped (fail-closed — an unjustified exception grants
nothing). This is the same shape as `SIMPLE_MC_ALLOC_ALLOW` so an operator
learns one grammar, and it is a single flat scalar because the typed
`ProjectContext` loader (`80.driver/project.spl`) reads the same `lints:`
dict and falls back to defaults on any shape it cannot parse.

## What is reported

CLI: `info: [lint] mission-critical exception: <path> -- <reason>
(critical-tier rules skipped; linted at strict)` before the file's findings.
JSON (`--json`): `{"type":"lint-mc-exception","file":...,"reason":...}`.
The file is still linted — at `strict` — so ordinary findings still print.

## Bootstrap (Stage 3) opt-in

`SIMPLE_STAGE3_MISSION_CRITICAL=1` makes `scripts/bootstrap/resume-stage3-from-admitted.sh`
and `bootstrap-from-scratch.sh` add `SIMPLE_SAFETY_PROFILE=critical
SIMPLE_ASSURANCE_WARNING_PHASE=1` to the Stage 3 environment (baked into the
args hash like the threads knob). Unset keeps the pinned argv byte-identical.
The Stage 2 bootstrap CLI already reads `SIMPLE_SAFETY_PROFILE`
(`80.driver/driver_types.spl:630`); it does NOT read `simple.sdn`'s
`lints:` pin and it does not run lint rules — only the driver safety pass.

## Promotion

Turning warnings back into errors is `warning_phase: false` (or deleting the
key) per package, once that package's census is zero. Do not promote a
package while it still has exceptions you have not decided on.

Spec: `test/01_unit/compiler/assurance/mc_warning_phase_exceptions_spec.spl`.
