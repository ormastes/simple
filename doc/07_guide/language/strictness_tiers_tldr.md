# Strictness Tiers — TL;DR

Code-strictness axis, **orthogonal** to stdlib memory tiers. Pick one of each; they compose.

- **moderate** — advisory; deny defaults → warn. Scripts/prototypes.
- **strict** — current defaults (regression-safe baseline). Library code.
- **robust** — Rust-parity strictness; safety/public-surface lints → deny. Ladder: lint → primitive-use warn+autofix → proof-coverage (rungs 2-3 planned).
- **critical** — robust + REQ-MC rules (bare-primitive-internal at warn). Mission-critical systems; planned for REQ5+.

Select (precedence): `@lint_profile(...)` > `simple lint --profile=...` > `simple.sdn [lints] profile=` > engine default. Unset = legacy behavior. `@lint_profile` ≠ `@profile(critical)` (R9 must-use). **Note:** compiler/loader defaults to `robust` at WARN severity (not ERROR).

```sdn
diagram {
  axis_A: "stdlib memory tier" -> [nogc_sync_mut, nogc_async_mut, gc_async_mut, noalloc]
  axis_B: "strictness tier"    -> [moderate, strict, robust, critical]
  compose: "any A x any B"     # e.g. noalloc + robust
  robust_critical_ladder: [lint, "primitive-use warn+autofix", "proof-coverage"]
  deprecated_names: [lib -> strict, reliable -> robust, mission-critical -> critical]
  compiler_loader_default: "robust (at WARN severity during migration)"
  supersedes: "High-robustness mode (rejected) -> configurable strict-lint + proof-coverage"
}
```

P0 shipped: tier selector + every lint code configurable (`simple lint`). Tier names renamed 2026-07-28; old names (`lib`, `reliable`, `mission-critical`/`mission_critical`) still work with deprecation warnings.
Full guide: `strictness_tiers.md` · Plan: `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` · Glossary: "Strictness Tiers".
