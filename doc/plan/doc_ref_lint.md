# Plan: Doc Reference & SDoctest Lint

**Feature:** `doc_ref_lint`
**Related:** [requirement](../requirement/doc_ref_lint.md) | [design](../design/doc_ref_lint.md) | [research](../research/doc_ref_lint.md)

---

## Task Breakdown

| # | Task | Difficulty | Model | Depends On |
|---|------|-----------|-------|------------|
| 1 | Parse `@see(X)` and `@sdoctest(X)` from doc comment text | 2 | sonnet | — |
| 2 | Build module declaration index (name → tag map) | 2 | sonnet | — |
| 3 | Detect sdoctest block in doc comment | 1 | haiku | — |
| 4 | PDOC001: Missing sdoctest on public fn | 2 | sonnet | 1, 2, 3 |
| 5 | PDOC002: Invalid reference target | 2 | sonnet | 1, 2 |
| 6 | PDOC003: Unused @see reference | 3 | sonnet | 1, body scan |
| 7 | PDOC004: @sdoctest type mismatch | 2 | sonnet | 1, 2 |
| 8 | PDOC005: Chained delegation no sdoctest | 2 | sonnet | 1, 2, 3 |
| 9 | Wire into lint pipeline + __init__.spl exports | 1 | haiku | 4-8 |
| 10 | System test (SSpec) | 2 | sonnet | 9 |

## Implementation Order

1. Tasks 1-3 (parallel — independent helpers)
2. Tasks 4-8 (sequential — all depend on helpers, build on each other)
3. Task 9 (wire up)
4. Task 10 (test)

All tasks fit in a single file: `src/compiler/35.semantics/lint/public_doc.spl`
