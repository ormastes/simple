# Anti-Dummy / Anti-Stub Enforcement Research

**Date:** 2026-04-04  
**Scope:** stronger ways to prevent placeholder tests, tautological assertions, and trivial stub implementations

## Summary

The strongest practical pattern for this repo is a layered approach:

1. **AST-level fast-fail linting** for obvious placeholders and trivial stubs
2. **repo-scoped audit/reporting** so legacy debt is visible and measurable
3. **method-level mutation or mutation-like checks** for high-value suites, because coverage and assertion count alone are weak proxies for test quality

This aligns with the current repo state:

- the tree still contains a large legacy backlog of placeholder tests
- fast local feedback is needed on every changed file
- the full repo cannot honestly be called clean until a measurable backlog is burned down

## Findings

### 1. Coverage is not enough

Method-level mutation research shows that strong coverage can still hide low-quality tests. High-quality tests correlate more with fewer critical test smells than with raw size or number of assertions.

Why it matters here:

- `expect(true).to_equal(true)` and similar placeholder-success patterns can still execute code and inflate perceived test confidence
- a lint gate is necessary, but long-term proof quality should also use mutation-style methods on high-value suites

Source:
- Veloso and Hora, *Characterizing High-Quality Test Methods: A First Empirical Study* (MSR 2022): [PDF](https://homepages.dcc.ufmg.br/~andrehora/pub/2022-msr-test-quality.pdf)

### 2. Method-level mutation is stronger than suite-level mutation for contribution quality

The same study argues that whole-suite mutation scores can hide weak contributed tests, because existing tests can kill mutants that the new test never meaningfully checks.

Why it matters here:

- current repo cleanup should not stop at “the suite is green”
- the right future direction is targeted mutation or mutation-like differential checks for changed tests/specs

Source:
- Veloso and Hora (same paper): [PDF](https://homepages.dcc.ufmg.br/~andrehora/pub/2022-msr-test-quality.pdf)

### 3. Test-smell detection should be explicit and automated

The practical lesson from the literature is that critical test smells should be surfaced directly, not inferred only through style review or coverage dashboards.

Why it matters here:

- placeholder pass helpers
- tautological literal assertions
- fake success arms inside `match`
- local suppression of those lints

should all be audit-visible and preferably fail in changed-scope verification

## Strongest Patterns To Apply In This Repo

### Fast path

- keep AST-based deny lints for:
  - tautological assertions
  - placeholder pass helpers
  - fake `Ok(_)` / `Err(_)` success arms
  - obvious stub implementations
- treat local suppression of those lints as verify debt

### Audit path

- generate a verify report for current changes
- support `--all` audits over `test/` and `src/`
- count and report remaining offenders by file/path

### Hardening path

- add a backlog tracker for legacy offenders
- migrate placeholder-heavy suites incrementally
- add mutation-style checks later for high-value suites rather than the whole repo at once

## Recommended Repo Direction

### Implement now

- project-scoped anti-dummy / anti-stub verify gate
- explicit report artifact
- backlog tracking for legacy offenders

### Implement later

- method-level mutation checks for changed test methods in critical suites
- stronger semantic detection for empty examples and assertion-free examples
- CI policy that blocks net-new placeholder debt even before the repo-wide backlog reaches zero

## Sources

- Victor Veloso, Andre Hora. *Characterizing High-Quality Test Methods: A First Empirical Study* (MSR 2022): https://homepages.dcc.ufmg.br/~andrehora/pub/2022-msr-test-quality.pdf
