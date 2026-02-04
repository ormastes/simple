# Parser Duplication Merge - Complete Summary

**Date:** 2026-02-04
**Status:** Ready for Implementation

---

## Overview

Two parser duplications identified and planned for merge:

1. **Lexer Duplication** → Simple deletion (5 min)
2. **TreeSitter Merge** → Add heuristic mode (5-7 hours)

**Total Effort:** ~5-7 hours
**Code Reduction:** ~2,163 lines

---

## Merge 1: Lexer (SIMPLE - NO MERGE NEEDED)

### Current State

- `compiler/lexer.spl` (1,268 lines) - ✅ **USED** by compiler
- `app/parser/lexer.spl` (1,654 lines) - ❌ **NOT USED** anywhere

### Finding

**ZERO imports** of duplicate lexer found! It's dead code.

### Action

**Just delete** - no merge needed:

```bash
rm src/app/parser/lexer.spl
```

**Effort:** 5 minutes
**Code Reduction:** 1,654 lines

---

## Merge 2: TreeSitter (ADD HEURISTIC MODE)

### Current State

- `compiler/treesitter.spl` (1,444 lines) - ✅ **USED** (token-based, strict)
- `compiler/parser/treesitter.spl` (509 lines) - ❌ **NOT USED** (line-based, error-tolerant)

### Goal

**Add error-tolerant mode** to heavyweight TreeSitter for LSP/IDE use.

### Strategy

Port line-based algorithm into main TreeSitter:

```simple
struct TreeSitter:
    heuristic_mode: bool  # NEW: Enable error-tolerant parsing

impl TreeSitter:
    me parse_outline() -> OutlineModule:
        if self.heuristic_mode:
            self.parse_outline_heuristic()  # Line-based, tolerant
        else:
            self.parse_outline_token_based()  # Token-based, strict
```

**Benefit:** Error tolerance for incomplete/broken code (LSP/IDE)

**Effort:** 5-7 hours
**Code Reduction:** 509 lines (delete old file after merge)

### Phases

1. Add `heuristic_mode` field (30 min)
2. Port helper types (30 min)
3. Port line-based algorithm (2-3 hours)
4. Data conversion (1-2 hours)
5. Testing (1 hour)
6. Cleanup (15 min)
7. Documentation (30 min)

---

## Combined Results

### Before Merge

| File | Lines | Status |
|------|-------|--------|
| `compiler/lexer.spl` | 1,268 | ✅ Used |
| `app/parser/lexer.spl` | 1,654 | ❌ Unused |
| `compiler/treesitter.spl` | 1,444 | ✅ Used |
| `compiler/parser/treesitter.spl` | 509 | ❌ Unused |
| **TOTAL** | **4,875** | |

### After Merge

| File | Lines | Status |
|------|-------|--------|
| `compiler/lexer.spl` | 1,268 | ✅ Canonical |
| `compiler/treesitter.spl` | ~1,700 | ✅ Dual-mode (token + heuristic) |
| **TOTAL** | **~2,968** | |

**Code Reduction:** 1,907 lines (39%)

---

## Implementation Order

### Option A: Sequential (Recommended)

1. **Delete lexer** (5 min)
   - Simple cleanup, no risk
2. **Merge treesitter** (5-7 hours)
   - Complex merge, test thoroughly

**Total Time:** ~5-7 hours

### Option B: Parallel

Both are independent, can be done simultaneously.

---

## Quick Commands

```bash
# Backup state
jj bookmark create backup-before-duplication-merge

# Merge 1: Delete unused lexer
rm src/app/parser/lexer.spl
rmdir src/app/parser  # If empty

# Merge 2: Follow detailed plan
# See: doc/plan/treesitter_heuristic_merge_plan_2026-02-04.md

# Test
simple test

# Build
simple build --release

# Commit
jj bookmark set main -r @
jj commit -m "refactor: Remove parser duplications (1,907 lines)"
jj git push --bookmark main
```

---

## Related Documentation

- **Research:** `doc/research/parser_duplication_analysis_2026-02-04.md`
- **Design:** `doc/design/parser_architecture_unified_2026-02-04.md`
- **Lexer Plan:** `doc/plan/parser_merge_plan_2026-02-04.md` (obsolete - just delete)
- **TreeSitter Plan:** `doc/plan/treesitter_heuristic_merge_plan_2026-02-04.md` ⭐
- **File Locations:** `doc/architecture/parser_file_locations_2026-02-04.md`

---

**Status:** ✅ Plans Complete - Awaiting approval to proceed
