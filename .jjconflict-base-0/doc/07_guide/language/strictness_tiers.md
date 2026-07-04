# Strictness Tiers (Script Modes)

Simple has **two independent classification axes**. Do not conflate them:

| Axis | Controls | Values |
|------|----------|--------|
| **Stdlib memory tier** | runtime / allocation / async model | `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc` (see `.claude/rules/structure.md`) |
| **Strictness tier** (this guide) | code-quality strictness: which lints fire, at what severity, and whether proof-coverage is gated | `moderate`, `lib`, `reliable` |

A build target picks one value on **each** axis; they compose freely — e.g. a
`nogc_async_mut_noalloc` baremetal module can be built under `reliable`.
"reliable" is **not** a memory tier and never changes the runtime model.

## The three tiers

| Tier | Audience | Lint behavior |
|------|----------|---------------|
| **moderate** | scripts, prototypes, examples | advisory only — every `deny` default is downgraded to `warn` |
| **lib** | library / reusable code | current defaults (the regression-safe baseline) |
| **reliable** | safety-relevant units | strictest — public-surface + safety/correctness lints elevated to `deny` |

`reliable` is a **ladder**:
1. current lint level (run at compile and, planned, link),
2. local/internal-primitive-use check surfaced as a WARNING with verified auto-fix (planned),
3. formal-verification **coverage** meta-check — each feature-level public class /
   main-class-of-file *has* a discharged proof (planned; a coverage check, not a prover).

> Rungs 2–3 are on the roadmap. See
> `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` for the phased plan.
> Today (P0) the tier selector and per-lint configurability ship for `simple lint`.

## Selecting a tier

Three sources, **most-local-wins** precedence (`@lint_profile` > `--profile` > sdn):

```sdn
# simple.sdn — project default
[lints]
profile = "reliable"
primitive_api = "deny"   # explicit per-lint override still wins over the tier
```

```bash
simple lint src/foo.spl --profile=reliable   # CLI override
```

```simple
@lint_profile(reliable)   # file-header attribute (top of file, before defs)

# NOTE: distinct from @profile(critical), the R9 must-use annotation.
```

When no tier is selected, behavior is identical to today's defaults (the legacy
baseline) — selecting a tier is opt-in.

## Per-lint configuration

Every lint code now maps to a stable config name, so any lint is governable via
`[lints]` / `@allow(...)` / `@warn(...)` / `@deny(...)`. Newly-configurable
families include: `unused_code` (W001-3), `style_convention` (ST001-3),
`unsafe_pattern` (S001-3), `concurrency_misuse` (CC001-2), `closure_capture`
(CLOS001), `ignored_return` (RET001), `multiline_bool` (BOOL001),
`memory_safety` (SAFE001/3), `visibility_boundary` (W0401-3),
`database_integrity` (D001), `tracking_traceability` (TRK001).

## Relationship to the rejected "High-robustness mode"

`reliable` supersedes the previously-rejected "High-robustness mode"
(`simple_language_comparison.md`). Instead of an unprovable blanket guarantee, it
is the configurable strict-lint + `@deny(non_exhaustive_match)` + proof-coverage
realization that document prescribed — dialed by context, not asserted.

See also: `doc/glossary.md` ("Strictness Tiers"), `strictness_tiers_tldr.md`.
