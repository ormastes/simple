---
name: refactor
description: "Code quality refactoring workflow — 5 phases: file size, duplication, coupling, Big-O, test verification. Use when cleaning up code."
---

# Refactor Skill — Code Quality Workflow

## Phase 1: File Size & Structure
- **800 lines max** per source file. Split oversized files with meaningful names (NOT `xx_1.spl`)
- Update all imports after splitting. Confirm each deletion/move with user.
- Intentional exceptions: `#![allow(large_file)]  # Intentional: <reason>`

## Phase 2: Duplication Removal

```bash
bin/simple duplicate-check <dir> --min-lines 5           # Token duplication
bin/simple duplicate-check <dir> --cosine --min-lines 5   # Structural similarity
bin/simple duplicate-check <dir> --semantic               # Same-intent detection
```

Fix: extract shared helpers, use parameter objects for repeated param lists (3+).

## Phase 3: Coupling Measurement

| Metric | Target |
|--------|--------|
| CBO (coupled classes) | < 8 |
| Fan-out (dependencies) | < 10 |
| SCC cycles | 0 |
| RFC (methods + called) | < 50 |
| LCOM (cohesion) | Close to 0 |

Layer violations: deps must flow downward through `src/compiler/NN.name/` layers.

```bash
bin/simple query workspace-symbols --query <symbol>
bin/simple query references <file> <line>
```

## Phase 4: Big-O Analysis
For each public function, identify complexity. Flag O(n^2)+:
- Nested loops over same collection -> hash lookup
- String concat in loops -> builder
- `arr + [item]` in loops -> `.push()`
- Re-reading files/recomputing in loops -> cache/hoist

## Phase 5: Test Verification

```bash
bin/simple test && bin/simple build lint && bin/simple build check
```

Run after EACH phase. NEVER skip failing tests. Fix refactoring, not tests.

## Critical Rules
- All code in `.spl` — no Python, no Bash
- Generics: `<>` not `[]`
- No inheritance — use composition, traits, mixins
