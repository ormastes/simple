# Refactor Skill

## Phase 1: Big-Class Extraction & Structure

- **Source files:** 800 lines max. Split oversized files/classes with meaningful names (NEVER `xx_1.spl`, `part1`, `v1`).
- Update all imports after splitting. Confirm each deletion/move with user.
- Intentional exceptions: `#![allow(large_file)]  # Intentional: <reason>`

### Splitting a big class — methodology (in order)

1. **Try to extract a class.** Before splitting a file mechanically, ask whether
   a cohesive sub-responsibility wants to become its own class/type. Prefer
   extracting a real class over slicing one class across files.
2. **Divide by the semantic of the class description.** Read the class/type
   doc-comment. Group methods by what the description says the class *does*; each
   semantic group becomes a file (or extracted class).
3. **Check cohesion & coupling to decide the cut.** Keep methods that share
   fields/state together (high cohesion); cut along the seam with the fewest
   cross-references (low coupling). Use the Phase 3 metrics (LCOM, CBO, fan-out)
   to confirm the cut lowers coupling, not just line count.
4. **Name by meaning, never by number.** Each piece gets a domain/behavior name
   (`token_scanner.spl`, `error_recovery.spl`), never `_1`/`_2`/`part`/`ver`/`v1`.
5. **Use the highest-capability model to choose the division** (or, if a
   lower/least-verified model proposed it, have the highest model review and
   accept the split). Record which model decided the division in the commit/state.

### `_ClassName/` folder for split classes

When a single class is split across multiple files, **put the pieces in a
`_ClassName/` folder** instead of leaving sibling numbered files:

- **Existing numbered class-splits** (`foo_part1.spl`, `foo_2.spl`, …): move them
  into a `_ClassName/` folder and rename each file by semantic meaning.
- **Simple-lang classes:** create `_ClassName/`, move `ClassName.spl` into it,
  and do the further semantic split *inside* that folder.
- The leading `_` makes the folder a **transparent package**: its files resolve
  as if they sat directly in the parent folder, so siblings and sibling folders
  still see `ClassName` with no new `use`. Applies recursively, so a
  `_ClassName/` can itself contain a deeper `_sub/` whose files bubble up.
- A `_ClassName/` folder is a stepping stone — once it grows its own cohesive
  surface it can be promoted to a real `_package/` (still transparent) or a plain
  `package/` (addressable, needs `use`) with its own siblings.

See `doc/04_architecture/compiler/misc/underscore_folder_package.md` for the
language semantics. Fix any `private-symbol`/`unused`/import warnings the move
introduces.

## Phase 2: Duplication Removal

```bash
bin/simple duplicate-check <dir> --min-lines 5        # Token duplication (5+ lines)
bin/simple duplicate-check <dir> --cosine --min-lines 5  # Structural similarity
bin/simple duplicate-check <dir> --semantic            # Same-intent detection
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

**Layer violations**: deps must flow downward through `src/compiler/NN.name/` layers.

```bash
bin/simple query workspace-symbols --query <symbol>   # Find symbols
bin/simple query references <file> <line>              # Trace dependencies
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

## Workflow

1. **Scan**: duplication checker, file sizes, coupling metrics
2. **Plan**: list issues, prioritize by impact
3. **Confirm**: show plan to user, get approval
4. **Fix**: one file at a time
5. **Verify**: tests after each change
6. **Report**: before/after metrics
