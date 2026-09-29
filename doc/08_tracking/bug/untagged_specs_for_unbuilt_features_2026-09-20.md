# Untagged specs for functionality that was never built read as regressions

- **id:** untagged_specs_for_unbuilt_features_2026-09-20
- **status:** OPEN — measured; the fix is a tagging/roadmap decision, not a code change
- **severity:** P3 individually, P2 in aggregate — it makes the suite's failure count uninterpretable
- **found:** 2026-09-20, running every test surface that had no verdict

## The pattern

Several suites fail on specs that exercise APIs the tree does not provide. None
of them carries `@tag:in-development`, `# @pending` or `# @skip`, so every
summary counts them as ordinary failures — indistinguishable from regressions.

| API the spec calls | exists in `src/`? | failing specs |
|---|---|---|
| `TreeSitter.new(...)` | **no `class TreeSitter` anywhere** | 12 (`test/feature/usage`) |
| `std.parser.treesitter_node` | exports nothing of that name | 1 (`01_unit/std/parser`) |
| `Mock` | not defined | 2 (`01_unit/std`) |
| `before_all` / `after_all` | not defined | 2 (`01_unit/std`) |
| `extract_directive_lines` bare, `@skip_mode:` literal | existed; spec was wrong | 1 — **fixed**, PR #1148 |

The last row is the useful contrast: it looked identical from the outside — a
spec failing on `function ... not found` — but there the functions **did** exist
and the spec was simply wrong, so it was a real fix. Distinguishing the two
needs someone to check whether the callee exists, which no failure count does.

## Verification

Checked directly, not inferred:

```
grep -rn "class TreeSitter" src/ --include=*.spl
  -> only TreeSitterAnalysis / TreeSitterParsedCommand, in an unrelated
     app module (llm_caret/claude_full/utils/bash/ParsedCommand.spl)

find src/lib -name "treesitter_node*"    -> nothing
grep -rl "fn before_all" src/            -> nothing
```

And the tags:

```
for each failing spec: grep -E "@tag:.*in-development|# @pending|# @skip"
  -> 0 of 9 in std, 0 of 38 in feature
```

## Why it matters

`test/03_system/core/error_path` shows the other half of the same problem from
the opposite direction: 100 specs fail there, all on one generated scenario
(`error path 27 - option chain breaks`), and the spec's own docstring says

> is **RED by contract**: `Some(nil).?` is false on the current runtime, and the
> scenario keeps asserting the truth of that unwrap so the defect stays visible
> instead of being softened.

That is a deliberate tripwire — correct behaviour, counted as 100 failures.

So of ~2,690 failing spec files measured this session, at least **119** are
known not to be regressions: 100 deliberate reds, 13 unbuilt `TreeSitter`, and
~6 other unbuilt APIs. The true defect count is lower than any summary reports,
and nobody can tell which is which without reading each spec.

## What would fix it

Tag the unbuilt-API specs `@tag:in-development` so they are skipped-but-counted
per `doc/07_guide/infra/testing.md`, and give the red-by-contract scenarios a
marker that distinguishes "deliberately red" from "broken". Both are decisions
for the owners of those areas — treesitter, the mock framework, the spec
runner's `before_all` support — not a unilateral edit from a triage pass, which
is why this is a record rather than a patch.

## Related

- `doctest_surfaces_registered_but_not_executed_2026-09-19` — same theme: a
  surface that appears maintained and is not.
- `std_suite_failures_are_unbuilt_features_2026-09-20` — the per-suite detail
  for `01_unit/std`, including the one genuine concurrency defect in it.
