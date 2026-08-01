# Strictness Tiers (Script Modes)

Simple has **two independent classification axes**. Do not conflate them:

| Axis | Controls | Values |
|------|----------|--------|
| **Stdlib memory tier** | runtime / allocation / async model | `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc` (see `.claude/rules/structure.md`) |
| **Strictness tier** (this guide) | code-quality strictness: which lints fire, at what severity, and whether proof-coverage is gated | `moderate`, `strict`, `robust`, `critical` |

A build target picks one value on **each** axis; they compose freely — e.g. a
`nogc_async_mut_noalloc` baremetal module can be built under `robust`.
Strictness tiers are **not** memory tiers and never change the runtime model.

## The four tiers

| Tier | Audience | Lint behavior |
|------|----------|---------------|
| **moderate** | scripts, prototypes, examples | advisory only — every `deny` default is downgraded to `warn` |
| **strict** | library / reusable code | current defaults (the regression-safe baseline) |
| **robust** | safety-relevant units | Rust-parity level — public-surface + safety/correctness lints elevated to `deny` |
| **critical** | mission-critical systems | robust + REQ-MC rules (`bare_primitive_internal` at `warn`); planned for REQ5+ |

The **robust** and **critical** tiers are part of a **ladder**:
1. strict lint levels (currently run at compile; planned to also run at link),
2. local/internal-primitive-use check surfaced as a WARNING with verified auto-fix (planned),
3. formal-verification **coverage** meta-check — each feature-level public class /
   main-class-of-file *has* a discharged proof (planned; a coverage check, not a prover).

> Rungs 2–3 are on the roadmap. See
> `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` for the phased plan.
> Today (P0) the tier selector and per-lint configurability ship for `simple lint`.

## Selecting a tier

Five sources with precedence (**highest to lowest**):
1. `@lint_profile(...)` — file-header attribute (top of file, before defs)
2. `--profile=...` — explicit CLI flag
3. `simple.sdn [lints] profile=...` — project default
4. engine default — `moderate` (interpreter/JIT), `robust` at WARN severity (compiler/loader)
5. legacy baseline — if no tier selected above, behavior is identical to today's defaults

Examples:

```sdn
# simple.sdn — project default
[lints]
profile = "robust"
primitive_api = "deny"   # explicit per-lint override still wins over the tier
```

```bash
simple lint src/foo.spl --profile=robust   # CLI override
```

```simple
@lint_profile(critical)   # file-header attribute (top of file, before defs)

# NOTE: distinct from @profile(critical), the R9 must-use annotation.
```

**Note on compiler/loader defaults:** native builds and module loading use the `robust` tier by default, but all its `deny`-level rules run at `warn` severity during the migration window. Escalation to `error` is a later change, explicitly not yet implemented.

## Deprecated tier aliases (pre-2026-07-28)

The tier names were renamed on 2026-07-28 for clarity. Old spellings still work but emit a one-time deprecation warning per distinct old name:

| Old name | New name |
|----------|----------|
| `lib` | `strict` |
| `reliable` | `robust` |
| `mission-critical` or `mission_critical` | `critical` |
| `moderate` | `moderate` (unchanged) |

Configs using old names continue to work with no behavior change — only the names have changed, not the semantics. Update your configs at your convenience.

## Per-lint configuration

Every lint code now maps to a stable config name, so any lint is governable via
`[lints]` / `@allow(...)` / `@warn(...)` / `@deny(...)`. Newly-configurable
families include: `unused_code` (W001-3), `style_convention` (ST001-3),
`unsafe_pattern` (S001-3), `concurrency_misuse` (CC001-2), `closure_capture`
(CLOS001), `ignored_return` (RET001), `multiline_bool` (BOOL001),
`memory_safety` (SAFE001/3), `visibility_boundary` (W0401-3),
`database_integrity` (D001), `tracking_traceability` (TRK001).

## Relationship to the rejected "High-robustness mode"

The `robust` and `critical` tiers supersede the previously-rejected "High-robustness mode"
(`simple_language_comparison.md`). Instead of an unprovable blanket guarantee, they
realize the configurable strict-lint + `@deny(non_exhaustive_match)` + proof-coverage
approach that document prescribed — dialed by context, not asserted. `critical` adds
mission-critical safeguards like bare-primitive-internal tracking.

See also: `doc/glossary.md` ("Strictness Tiers"), `strictness_tiers_tldr.md`.
