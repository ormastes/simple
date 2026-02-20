# Docs Agent - Documentation Writing

**Use when:** Writing research docs, design docs, requirement docs, feature specs, guides, reports, updating TODO tracking.
**Skills:** `/doc`, `/todo`, `/rule`, `/sspec`

## Documentation Types

| Type | Location | When to Use |
|------|----------|-------------|
| Plan | `doc/plan/` | Project plans: why, scope, milestones, risks |
| Requirement | `doc/requirement/` | User request + interpretation + REQ-NNN statements |
| Feature Spec | `doc/feature/` | BDD scenarios derived from requirements |
| NFR / SLO | `doc/nfr/` | Performance, reliability, security targets |
| Research | `doc/research/` | Investigation, options analysis, benchmarks |
| Design | `doc/design/` | Architecture decisions, component design |
| ADR | `doc/adr/` | Architecture Decision Records (major decisions) |
| Guide | `doc/guide/` | User-facing tutorials, runbooks, how-to |
| Report | `doc/report/` | Session summaries, completion reports |
| BDD Tests | `test/*_spec.spl` | Executable feature specs (SSpec) |

## Document Relationship Model

```
PLAN → REQUIREMENTS → FEATURE SPEC → BDD TESTS → TEST RESULTS
                    ↘ NFR
RESEARCH → DESIGN → ADR
RULES → enforced by CI + review
```

## Critical Rules

- Specifications MUST be SSpec test files (`*_spec.spl`), not markdown
- Research goes in `doc/research/`, NOT mixed with specs
- Reports use format: `doc/report/<topic>_<date>.md`
- DO NOT add reports to jj unless requested

## Auto-Generated Docs (Updated Every Test Run)

- `doc/feature/feature.md` - All features
- `doc/feature/pending_feature.md` - Incomplete features
- `doc/test/test_result.md` - Test results + timing
- `doc/build/recent_build.md` - Build errors/warnings

## TODO Format

```simple
# TODO: [area][priority] description [#issue] [blocked:#issue]
# Areas: doc, runtime, parser, stdlib, compiler, testing, tooling, design
# Priorities: P0 (critical), P1 (high), P2 (medium), P3 (low)
```

## Writing Style

- Clear and concise, no fluff
- Active voice, present tense
- Working code examples (copy-pasteable)
- Use markdown tables for comparisons
- Cross-reference with relative links

## Report Template

```markdown
# Topic - Report

**Date:** YYYY-MM-DD
**Status:** Complete/In Progress

## Summary
1-2 paragraph overview.

## Changes Made
- File: description of change

## Results
- Before: X
- After: Y

## Next Steps
- [ ] Task 1
```

## See Also

- `/doc` - Full documentation workflow
- `/todo` - TODO/FIXME format specification
