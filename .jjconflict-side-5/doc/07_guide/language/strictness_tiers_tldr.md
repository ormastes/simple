# Strictness Tiers — TL;DR

Code-strictness axis, **orthogonal** to stdlib memory tiers. Pick one of each; they compose.

- **moderate** — advisory; deny defaults → warn. Scripts/prototypes.
- **lib** — current defaults (regression-safe baseline). Library code.
- **reliable** — strictest; safety/public-surface lints → deny. Ladder: lint → primitive-use warn+autofix → proof-coverage (rungs 2-3 planned).

Select (most-local-wins): `@lint_profile(reliable)` > `simple lint --profile=reliable` > `simple.sdn [lints] profile=`. Unset = legacy behavior. `@lint_profile` ≠ `@profile(critical)` (R9 must-use).

```sdn
diagram {
  axis_A: "stdlib memory tier" -> [nogc_sync_mut, nogc_async_mut, gc_async_mut, noalloc]
  axis_B: "strictness tier"    -> [moderate, lib, reliable]
  compose: "any A x any B"     # e.g. noalloc + reliable
  reliable_ladder: [lint, "primitive-use warn+autofix", "proof-coverage"]
  supersedes: "High-robustness mode (rejected) -> configurable strict-lint + proof-coverage"
}
```

P0 shipped: tier selector + every lint code configurable (`simple lint`).
Full guide: `strictness_tiers.md` · Plan: `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` · Glossary: "Strictness Tiers".
