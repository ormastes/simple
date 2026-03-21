# Refactor Skill

Comprehensive code quality refactoring workflow. Run all checks, fix issues, verify with tests.

## Phase 1: File Size & Structure

### Size Limits
- **Source files:** 800 lines max (except doc DBs and explicitly specified files)
- **CLAUDE.md:** 200 lines max (move details to skills)
- **Skill files:** No limit but keep focused

### Splitting Oversized Files
- Extract into files with **meaningful names** (NOT `xx_1.spl`, `xx_2.spl`)
- Validate each new filename describes its content - reject if ambiguous
- Update all imports after splitting
- Confirm each deletion/move with user before applying

### Intentional Exceptions
- Files that cannot be split further (monolithic by design) must be marked:
  ```simple
  #![allow(large_file)]  # Intentional: <reason>
  ```

---

## Phase 2: Duplication Removal

### Line Duplication (5+ lines)
```bash
bin/simple src/compiler/90.tools/duplicate_check/run_check.spl <dir> 5
```
- Fix by extracting shared helper functions
- Use parameter objects for repeated param lists
- Remaining intentional dups must be documented

### Cosine Duplication (structural similarity)
```bash
bin/simple duplicate-check <dir> --cosine --min-lines 5
```
- Detects renamed-variable clones
- Fix by extracting shared logic with parameters for differences

### Semantic Duplication (doc similarity)
```bash
bin/simple duplicate-check <dir> --semantic
```
- Detects same-intent different-implementation patterns
- Fix by choosing one implementation and delegating

### Parameter Object Pattern
When 3+ parameters repeat across functions:
```simple
# Before (duplicated params)
fn process(name: text, path: text, config: Config, verbose: bool): ...
fn validate(name: text, path: text, config: Config, verbose: bool): ...

# After (parameter object)
struct ProcessContext:
    name: text
    path: text
    config: Config
    verbose: bool

fn process(ctx: ProcessContext): ...
fn validate(ctx: ProcessContext): ...
```

---

## Phase 3: Coupling Measurement

### Static Analysis Pipeline
```
source code -> AST/symbol table -> dependency graph (V,E) -> metrics
```

### Metrics to Compute

| Metric | What | Target |
|--------|------|--------|
| **CBO** | Coupling Between Objects - count of coupled classes | < 8 |
| **Fan-in** | How many modules depend on this one | High = stable core |
| **Fan-out** | How many modules this one depends on | < 10 |
| **Instability** | fan-out / (fan-in + fan-out) | 0=stable, 1=unstable |
| **SCC cycles** | Strongly Connected Components - circular deps | 0 cycles |
| **DSM** | Dependency Structure Matrix - visual coupling grid | No below-diagonal |
| **RFC** | Response For a Class - methods + called methods | < 50 |
| **LCOM** | Lack of Cohesion of Methods - unused field groups | Close to 0 |

### Layer Violations
Check that dependencies flow downward through compiler layers:
```
00.common -> 10.frontend -> 15.blocks -> 20.hir -> 25.traits ->
30.types -> 35.semantics -> 40.mono -> 50.mir -> 55.borrow ->
60.mir_opt -> 70.backend -> 80.driver -> 85.mdsoc -> 90.tools ->
95.interp -> 99.loader
```
Any upward dependency is a **layer violation**.

### Public API Minimization
- Measure **public API entropy**: `H = -sum(p_i * log(p_i))` over export frequencies
- Minimize public surface: only export what's needed by other modules
- High LCOM -> split class (methods don't share fields)
- High complexity + high public API -> encapsulate behind facade

---

## Phase 4: Big-O Analysis

For each public function:
1. Identify loops, recursion, data structure operations
2. Classify: O(1), O(log n), O(n), O(n log n), O(n^2), O(n^3), O(2^n)
3. Flag O(n^2)+ as potential issues
4. Check for:
   - Nested loops over same collection -> O(n^2)
   - Linear search where hash lookup possible -> O(n) vs O(1)
   - String concatenation in loops -> O(n^2) total
   - Repeated array copy (`arr + [item]`) instead of `.push()` -> O(n^2)
   - Unnecessary sorting when partial order suffices

### Bad Implementation Patterns
- `var x = []; for ...: x = x + [item]` -> use `x.push(item)`
- Nested `for` with `.contains()` -> use dict lookup
- Re-reading files in loops -> cache content
- Recomputing values in loops -> hoist out

---

## Phase 5: Test Verification

After all refactoring:
```bash
bin/simple test                    # All tests
bin/simple build lint              # Linter
bin/simple build check             # All checks
```
- **NEVER skip failing tests** without user approval
- Run tests after each phase, not just at the end
- If tests fail, fix the refactoring - don't modify tests to pass

---

## Workflow

1. **Scan** - run duplication checker, measure file sizes
2. **Plan** - list all issues found, prioritize by impact
3. **Confirm** - show plan to user, get approval for each deletion/move
4. **Fix** - apply changes one file at a time
5. **Verify** - run tests after each change
6. **Report** - show before/after metrics

### Agent Teams Pattern
Split work by region to parallelize:
- **compiler-frontend** (00-20)
- **compiler-middle** (25-40)
- **compiler-backend** (50-70)
- **compiler-driver** (80-99)
- **stdlib** (lib/)
- **app** (app/)
