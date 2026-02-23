# Parser/Lexer Merge Plan - Step-by-Step Implementation

**Date:** 2026-02-04
**Status:** Implementation Plan
**Related:**
- `doc/research/parser_duplication_analysis_2026-02-04.md` - Duplication analysis
- `doc/design/parser_architecture_unified_2026-02-04.md` - Unified architecture design

---

## Overview

This document provides step-by-step instructions for merging duplicate parser/lexer implementations into a single canonical source.

**Timeline:** 5-11 hours over 2 days
**Risk Level:** Medium (many files affected, but well-tested components)

---

## Pre-Merge Audit

### Step 1: Find All Imports of Duplicate Lexer

```bash
cd /home/ormastes/dev/pub/simple

# Find all files importing app.parser.lexer
grep -r "from.*app\.parser\.lexer" src/ test/
grep -r "use.*app\.parser\.lexer" src/ test/
grep -r "import.*app\.parser\.lexer" src/ test/

# Save results for later
grep -r "app\.parser\.lexer" src/ test/ > /tmp/lexer_imports.txt
```

**Expected:** List of all files that need import updates

---

### Step 2: Identify Unique Features in app/parser/lexer.spl

**Method:** Side-by-side comparison

```bash
# Extract method signatures from both lexers
grep "fn \|me " src/app/parser/lexer.spl > /tmp/app_lexer_methods.txt
grep "fn \|me " src/compiler/lexer.spl > /tmp/compiler_lexer_methods.txt

# Compare
diff /tmp/app_lexer_methods.txt /tmp/compiler_lexer_methods.txt
```

**Look for:**
1. Methods in `app/parser/lexer.spl` NOT in `compiler/lexer.spl`
2. Different method signatures
3. Different field names
4. Unique token kinds

**Document findings in:** `/tmp/lexer_unique_features.md`

---

### Step 3: Check for Test Dependencies

```bash
# Find tests importing duplicate lexer
grep -r "app\.parser\.lexer" test/

# Run tests that use app lexer
simple test --list | grep lexer
```

**Expected:** List of tests that may fail after merge

---

## Phase 1: Lexer Merge (Day 1)

### Step 1.1: Backup Current State

```bash
# Create backup branch (using jj)
jj bookmark create backup-before-lexer-merge
```

---

### Step 1.2: Migrate Unique Features

**Read both lexers:**

```bash
# Open both files for comparison
less src/app/parser/lexer.spl
less src/compiler/lexer.spl
```

**Features to migrate (if needed):**

#### Feature A: `pending_tokens` Buffer

**Location:** `src/app/parser/lexer.spl:23`

```simple
pending_tokens: [Token]
```

**Check if used:**
```bash
grep -n "pending_tokens" src/app/parser/lexer.spl
```

**If used:** Add to `compiler/lexer.spl` struct definition

**Action:**
- [ ] Check if `pending_tokens` is used
- [ ] If yes, add field to `compiler/lexer.spl` Lexer struct
- [ ] If yes, copy related methods (`push_pending`, `pop_pending`, etc.)
- [ ] If no, document why it's not needed

---

#### Feature B: `force_indentation_depth`

**Location:** `src/app/parser/lexer.spl:26`

```simple
force_indentation_depth: i64
```

**Methods:**
```simple
me enable_forced_indentation()
me disable_forced_indentation()
```

**Check if used:**
```bash
grep -r "force_indentation\|enable_forced\|disable_forced" src/
```

**If used:** Add to `compiler/lexer.spl`

**Action:**
- [ ] Check if `force_indentation_depth` is used
- [ ] If yes, add field and methods to `compiler/lexer.spl`
- [ ] If no, document why it's not needed

---

#### Feature C: `tokenize()` Method

**Location:** `src/app/parser/lexer.spl:47-55`

```simple
fn tokenize() -> [Token]:
    var tokens_: [Token] = []
    loop:
        val tok = self.next_token()
        val is_eof = tok.kind is TokenKind.Eof
        tokens_.push(tok)
        if is_eof:
            break
    tokens_
```

**Check if `compiler/lexer.spl` has equivalent:**
```bash
grep -A 10 "fn tokenize" src/compiler/lexer.spl
```

**If missing:** Add to `compiler/lexer.spl`

**Action:**
- [ ] Check if `compiler/lexer.spl` has `tokenize()` method
- [ ] If no, add it with same signature
- [ ] Test: `simple test --tag=lexer`

---

### Step 1.3: Update Import Statements

**Get list of files to update:**

```bash
# Files importing app.parser.lexer
grep -rl "app\.parser\.lexer" src/ test/ > /tmp/files_to_update.txt
cat /tmp/files_to_update.txt
```

**For each file, update imports:**

```bash
# Example: Update a single file
sed -i 's/from app\.parser\.lexer/from compiler.lexer/g' src/some/file.spl
sed -i 's/use app\.parser\.lexer/use compiler.lexer/g' src/some/file.spl
sed -i 's/import app\.parser\.lexer/import compiler.lexer/g' src/some/file.spl
```

**Automated script:**

```bash
# Update all imports at once
while read -r file; do
    echo "Updating: $file"
    sed -i 's/from app\.parser\.lexer/from compiler.lexer/g' "$file"
    sed -i 's/use app\.parser\.lexer/use compiler.lexer/g' "$file"
    sed -i 's/import app\.parser\.lexer/import compiler.lexer/g' "$file"
done < /tmp/files_to_update.txt
```

**Manual review:**

```bash
# Review changes
for file in $(cat /tmp/files_to_update.txt); do
    echo "=== $file ==="
    grep "lexer" "$file" | head -5
done
```

**Action:**
- [ ] Run automated import update script
- [ ] Manually review first 5 files
- [ ] If patterns look correct, proceed with all
- [ ] Otherwise, adjust sed patterns and re-run

---

### Step 1.4: Delete Duplicate Lexer

**After verifying all imports are updated:**

```bash
# Remove duplicate lexer file
rm src/app/parser/lexer.spl

# Check if directory is now empty
ls src/app/parser/

# If empty, remove directory
if [ -z "$(ls -A src/app/parser/)" ]; then
    rmdir src/app/parser/
fi
```

**Action:**
- [ ] Verify all imports updated
- [ ] Delete `src/app/parser/lexer.spl`
- [ ] Remove directory if empty

---

### Step 1.5: Run Tests

```bash
# Run lexer-specific tests
simple test --tag=lexer

# Run parser tests (use lexer)
simple test --tag=parser

# Run all Simple tests
simple test --no-rust-tests

# Run Rust tests
simple build rust test

# Run full build
simple build --release
```

**If tests fail:**
1. Check error messages
2. Identify missing features
3. Add to `compiler/lexer.spl`
4. Re-run tests

**Action:**
- [ ] Run `simple test --tag=lexer`
- [ ] Run `simple test --tag=parser`
- [ ] Run `simple test`
- [ ] Run `simple build rust test`
- [ ] Fix any failures
- [ ] Re-run until all pass

---

### Step 1.6: Commit Changes

```bash
cd /home/ormastes/dev/pub/simple

# Add all changes
jj bookmark set main -r @

# Create commit message
cat > /tmp/commit_msg.txt <<EOF
refactor: Merge duplicate lexer into compiler/lexer.spl

Consolidated two lexer implementations into single canonical source.

Changes:
- Removed: src/app/parser/lexer.spl (1,654 lines)
- Kept: src/compiler/lexer.spl (1,268 lines)
- Updated all imports: app.parser.lexer → compiler.lexer
- Migrated unique features: [list features if any]

All tests passing:
- simple test: PASS
- simple build rust test: PASS
- simple build --release: SUCCESS

Related:
- doc/research/parser_duplication_analysis_2026-02-04.md
- doc/design/parser_architecture_unified_2026-02-04.md
- doc/plan/parser_merge_plan_2026-02-04.md
EOF

# Commit with message
jj commit -m "$(cat /tmp/commit_msg.txt)"

# Push to remote
jj git push --bookmark main
```

**Action:**
- [ ] Create commit with detailed message
- [ ] Push to remote

---

## Phase 2: TreeSitter Decision (Day 2)

### Option A: Keep Both (Recommended)

**Rationale:**
- `compiler/treesitter.spl` - Full outline parser (compiler use)
- `compiler/parser/treesitter.spl` - Lightweight heuristic parser (LSP/IDE use)
- Different purposes justify separate implementations

**Steps:**

#### Step 2A.1: Rename for Clarity

```bash
# Rename files to clarify purpose
# NOTE: Not actually renaming, just clarifying in documentation

# Add comments to both files
```

**Add to `src/compiler/treesitter.spl`:**

```simple
# TreeSitter - Full Outline Parser for Compiler
#
# This is the CANONICAL outline parser for Simple language compilation.
# Uses lexer for accurate tokenization and complete outline extraction.
#
# For LSP/IDE use cases (fast, heuristic parsing), see:
# - src/compiler/parser/treesitter.spl - Lightweight outline parser
#
# DO NOT duplicate this file. If you need outline parsing:
# - Compiler: Use this file (compiler/treesitter.spl)
# - LSP/IDE: Use compiler/parser/treesitter.spl
```

**Add to `src/compiler/parser/treesitter.spl`:**

```simple
# TreeSitter - Lightweight Outline Parser for LSP/IDE
#
# This is a fast, heuristic outline parser for IDE features.
# Uses indentation-based scanning (no full lexer) for speed.
# Tolerant of syntax errors, always produces results.
#
# For full compiler use (accurate, complete parsing), see:
# - src/compiler/treesitter.spl - Full outline parser
#
# Use cases:
# - LSP symbol extraction
# - IDE outline view
# - Quick navigation
# - Error region detection
# - Incremental updates
```

**Action:**
- [ ] Add clarifying comments to both files
- [ ] Update documentation to explain distinction

---

#### Step 2A.2: Update Documentation

**Create:** `doc/architecture/parser_lexer_structure.md`

```markdown
# Parser/Lexer/TreeSitter Structure

## Canonical Implementations

### Lexer: `src/compiler/lexer.spl`
- Full tokenization
- INDENT/DEDENT tracking
- String interpolation
- Math block mode
- Block registry integration

### Parser: `src/compiler/parser.spl`
- Full AST parsing
- Uses TreeSitter for outline
- Two-pass parsing

### TreeSitter: Two Implementations

#### 1. Full Outline Parser: `src/compiler/treesitter.spl`
**Use:** Compiler
**Features:** Complete outline extraction, uses Lexer
**Speed:** Medium (full tokenization)
**Accuracy:** High

#### 2. Lightweight Outline Parser: `src/compiler/parser/treesitter.spl`
**Use:** LSP/IDE
**Features:** Fast heuristic scanning, no full lexer
**Speed:** Fast (indentation-based)
**Accuracy:** Medium (tolerant of errors)

## Why Two TreeSitter Implementations?

Different use cases:
- **Compiler** needs accuracy, has time for full tokenization
- **LSP** needs speed, can tolerate heuristic parsing

Both are valid, serve different purposes, no duplication.
```

**Action:**
- [ ] Create `doc/architecture/parser_lexer_structure.md`
- [ ] Update `doc/architecture/file_tree.md` (if exists)
- [ ] Add cross-references in comments

---

#### Step 2A.3: Run Tests

```bash
# Test both treesitter implementations
simple test --tag=treesitter

# Full test suite
simple test
```

**Action:**
- [ ] Run tests
- [ ] Verify both implementations work
- [ ] Document in test results

---

#### Step 2A.4: Commit

```bash
jj bookmark set main -r @

cat > /tmp/commit_msg.txt <<EOF
docs: Clarify two TreeSitter implementations (no duplication)

Documented distinction between:
- compiler/treesitter.spl - Full outline parser (compiler)
- compiler/parser/treesitter.spl - Lightweight parser (LSP/IDE)

Both serve different purposes, no duplication to merge.

Added:
- Clarifying comments in both files
- doc/architecture/parser_lexer_structure.md
EOF

jj commit -m "$(cat /tmp/commit_msg.txt)"
jj git push --bookmark main
```

**Action:**
- [ ] Commit documentation updates

---

### Option B: Merge with Modes (Alternative)

**If user prefers single implementation:**

#### Step 2B.1: Merge Implementations

**Strategy:**
1. Use `compiler/treesitter.spl` as base
2. Add `fast_mode: bool` field (already exists!)
3. Implement heuristic mode in existing file
4. Delete `compiler/parser/treesitter.spl`

**Note:** `fast_mode` already exists in `compiler/treesitter.spl`!

**Check:**
```bash
grep -n "fast_mode" src/compiler/treesitter.spl
```

**If `fast_mode` already implemented:**
- Verify it provides LSP functionality
- If yes, delete `compiler/parser/treesitter.spl`
- If no, enhance `fast_mode` to match LSP needs

**Action (if merging):**
- [ ] Review `fast_mode` implementation
- [ ] Check if equivalent to lightweight parser
- [ ] If yes, update all imports
- [ ] Delete `compiler/parser/treesitter.spl`
- [ ] Run tests

---

## Phase 3: Documentation (Day 2)

### Step 3.1: Create Architecture Document

**Already created:**
- `doc/research/parser_duplication_analysis_2026-02-04.md`
- `doc/design/parser_architecture_unified_2026-02-04.md`

**Action:**
- [x] Research document created
- [x] Design document created
- [ ] Review for accuracy
- [ ] Update with merge results

---

### Step 3.2: Update File Tree Documentation

**Check if exists:**
```bash
ls doc/architecture/file_tree.md
```

**If exists, update:**

```markdown
# File Tree - Parser/Lexer Components

## Core Language Parsing (Simple Syntax)

### Lexer
- **src/compiler/lexer.spl** (1,268 lines) - ✅ CANONICAL
- src/compiler/lexer_types.spl - Token types

### Parser
- **src/compiler/parser.spl** (1,813 lines) - ✅ CANONICAL
- src/compiler/parser_types.spl - AST types

### TreeSitter
- **src/compiler/treesitter.spl** (1,444 lines) - ✅ CANONICAL (compiler)
- **src/compiler/parser/treesitter.spl** (509 lines) - ✅ Lightweight (LSP/IDE)
- src/compiler/treesitter_types.spl - Outline types

## Specialized Parsers (Other Languages/Formats)

### SDN Format
- src/lib/sdn/parser.spl (683 lines) - SDN parser
- src/lib/sdn/lexer.spl (411 lines) - SDN lexer

### IR DSL
- src/compiler/irdsl/parser.spl (147 lines) - IR DSL parser

### Predicates
- src/compiler/predicate_parser.spl (251 lines) - Predicate parser

### Tools
- src/app/depgraph/parser.spl (271 lines) - Import scanner
- src/app/ffi_gen/parser.spl (310 lines) - Annotation scanner
- src/app/test_runner_new/test_db_parser.spl (267 lines) - Test DB parser

### Convenience Wrappers
- src/app/interpreter/parser.spl (65 lines) - TreeSitter wrapper

## Removed

- ~~src/app/parser/lexer.spl~~ (1,654 lines) - ❌ DELETED (merged into compiler/lexer.spl)
```

**Action:**
- [ ] Update file tree documentation
- [ ] Mark removed files as deleted
- [ ] Clarify canonical vs specialized

---

### Step 3.3: Add Comments to Canonical Files

**Add to `src/compiler/lexer.spl`:**

```simple
# Lexer - Simple Language Lexical Analyzer
#
# ✅ CANONICAL IMPLEMENTATION
#
# This is the SINGLE SOURCE OF TRUTH for Simple language tokenization.
# All consumers (compiler, interpreter, LSP, tools) use this lexer.
#
# DO NOT create duplicate lexers. If you need custom tokenization:
# 1. Add modes/flags to this file (e.g., math_block mode)
# 2. Use specialized parsers for other languages (SDN, IR DSL, etc.)
# 3. Create thin wrappers if needed, but import THIS lexer
#
# Related:
# - parser.spl - Uses this lexer for parsing
# - treesitter.spl - Uses this lexer for outline parsing
# - doc/architecture/parser_lexer_structure.md - Architecture guide
```

**Add to `src/compiler/parser.spl`:**

```simple
# Parser - Simple Language Parser
#
# ✅ CANONICAL IMPLEMENTATION
#
# This is the SINGLE SOURCE OF TRUTH for Simple language parsing.
# Parses Simple source code into an Abstract Syntax Tree (AST).
# Uses tree-sitter for outline parsing, then detailed token-based parsing.
#
# DO NOT create duplicate parsers. If you need custom parsing:
# 1. Use specialized parsers for other languages (SDN, IR DSL, etc.)
# 2. Create thin wrappers if needed, but import THIS parser
#
# Related:
# - lexer.spl - Tokenizes source for parsing
# - treesitter.spl - Provides outline for two-pass parsing
# - doc/architecture/parser_lexer_structure.md - Architecture guide
```

**Action:**
- [ ] Add canonical comments to lexer
- [ ] Add canonical comments to parser
- [ ] Add canonical comments to treesitter

---

### Step 3.4: Create Migration Guide

**Create:** `doc/guide/parser_migration_guide.md`

```markdown
# Parser/Lexer Migration Guide

## For Contributors

### Old Import (Before Feb 4, 2026)

```simple
from app.parser.lexer import Lexer
```

### New Import (After Feb 4, 2026)

```simple
from compiler.lexer import Lexer
```

### What Changed?

- Merged duplicate lexer into `compiler/lexer.spl`
- Removed `src/app/parser/lexer.spl`
- All imports now use `compiler.lexer`

### If Your Code Breaks

1. Update imports: `app.parser.lexer` → `compiler.lexer`
2. Check if using app-specific features (unlikely)
3. Run tests: `simple test`

### Questions?

See:
- `doc/research/parser_duplication_analysis_2026-02-04.md` - Full analysis
- `doc/design/parser_architecture_unified_2026-02-04.md` - Architecture
```

**Action:**
- [ ] Create migration guide
- [ ] Link from main documentation

---

## Verification Checklist

### All Tests Pass

```bash
# Simple tests
simple test
# Expected: PASS (all tests)

# Rust tests
simple build rust test
# Expected: PASS (all tests)

# Build succeeds
simple build --release
# Expected: SUCCESS
```

**Action:**
- [ ] Run all tests
- [ ] Fix any failures
- [ ] Document results

---

### No Broken Imports

```bash
# Check for remaining references to old lexer
grep -r "app\.parser\.lexer" src/ test/
# Expected: No results

# Check for broken imports
simple build 2>&1 | grep "cannot find\|not found"
# Expected: No errors
```

**Action:**
- [ ] Search for old imports
- [ ] Fix any remaining
- [ ] Verify build succeeds

---

### Documentation Updated

**Check:**
- [ ] `doc/research/parser_duplication_analysis_2026-02-04.md` - Created ✅
- [ ] `doc/design/parser_architecture_unified_2026-02-04.md` - Created ✅
- [ ] `doc/plan/parser_merge_plan_2026-02-04.md` - Created ✅ (this file)
- [ ] `doc/architecture/parser_lexer_structure.md` - To be created
- [ ] `doc/guide/parser_migration_guide.md` - To be created
- [ ] `doc/architecture/file_tree.md` - To be updated (if exists)
- [ ] Canonical file comments - To be added

---

### Performance Maintained

```bash
# Before merge (if measured)
cat /tmp/lexer_perf_before.txt

# After merge
simple test --tag=lexer --bench
# Expected: Similar or better performance
```

**Action:**
- [ ] Run benchmarks (if available)
- [ ] Compare before/after
- [ ] Document results

---

## Rollback Plan (If Needed)

**If merge causes major issues:**

```bash
# Restore from backup
jj bookmark list
jj checkout backup-before-lexer-merge

# Review what went wrong
jj log

# Cherry-pick good commits if any
jj rebase ...

# Push fixed state
jj git push --bookmark main --force
```

**Action (only if needed):**
- [ ] Identify issue
- [ ] Restore from backup
- [ ] Fix issue
- [ ] Re-attempt merge with fix

---

## Final Summary

### What Was Merged

- [x] Lexer: `app/parser/lexer.spl` → `compiler/lexer.spl`
- [ ] TreeSitter: Documented as separate (or merged if Option B)

### What Remains Separate

- ✅ SDN parser/lexer (different language)
- ✅ IR DSL parser (different language)
- ✅ Predicate parser (specialized sublanguage)
- ✅ Tool parsers (import scanner, annotation scanner, test DB)
- ✅ Interpreter wrapper (thin convenience wrapper)

### Files Removed

- ❌ `src/app/parser/lexer.spl` (1,654 lines)
- ❌ `src/app/parser/` directory (if empty)

### Documentation Created

- ✅ `doc/research/parser_duplication_analysis_2026-02-04.md`
- ✅ `doc/design/parser_architecture_unified_2026-02-04.md`
- ✅ `doc/plan/parser_merge_plan_2026-02-04.md`
- [ ] `doc/architecture/parser_lexer_structure.md`
- [ ] `doc/guide/parser_migration_guide.md`

### Tests Status

- [ ] `simple test`: PASS
- [ ] `simple build rust test`: PASS
- [ ] `simple build --release`: SUCCESS

---

## Next Steps

1. ✅ Research and design complete
2. ⏳ Begin Phase 1: Lexer merge
3. ⏳ Begin Phase 2: TreeSitter decision
4. ⏳ Begin Phase 3: Documentation
5. ⏳ Verification and testing
6. ⏳ Commit and push changes

**Ready to proceed with implementation!**

---

**Status:** ✅ Plan Complete - Awaiting user approval to execute
