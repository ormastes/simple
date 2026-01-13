# SSpec Bulk Migration - Production Workflow Guide

**Version:** 1.0
**Date:** 2026-01-12
**Status:** Production Ready
**Audience:** Development Team

---

## Quick Start

```bash
# 1. Backup
mkdir -p migration_backups/$(date +%Y%m%d_%H%M%S)
cp path/to/file_spec.spl migration_backups/$(date +%Y%m%d_%H%M%S)/

# 2. Migrate
simple migrate --fix-sspec-docstrings path/to/file_spec.spl

# 3. Convert assertions (manual)
# - Replace if/else → expect()
# - See doc/guide/sspec_assertion_conversion.md

# 4. Fill docstrings (manual)
# - Replace TODO with documentation
# - See pilot_conversion_example.spl

# 5. Test
simple path/to/file_spec.spl
```

---

## Overview

This guide provides the complete workflow for migrating print-based SSpec tests to intensive docstring format. Follow these steps for each file or batch of files.

### Migration Phases

1. **Automated:** Migration tool (1-2 minutes)
2. **Manual:** Assertion conversion (30-60 min/file)
3. **Manual:** Docstring enhancement (30-60 min/file)
4. **Review:** Testing and validation (15-30 min/file)

**Total Time Per File:** 75-150 minutes

---

## Detailed Workflow

### Phase 1: Preparation (5 minutes)

#### Step 1.1: Identify Files

```bash
# Find all print-based test files
find simple/std_lib/test/features -name "*_spec.spl" -type f \
  -exec grep -l "print('describe\|print(\"describe" {} \;
```

#### Step 1.2: Prioritize

**Recommended Order:**
1. Smallest files first (easier to learn)
2. Grouped by category (maintain context)
3. Most critical features (highest value)

**Create Batch List:**
```bash
# Example batch file
cat > migration_batch1.txt <<EOF
simple/std_lib/test/features/codegen/cranelift_spec.spl
simple/std_lib/test/features/ml/config_system_spec.spl
simple/std_lib/test/features/language/imports_spec.spl
EOF
```

#### Step 1.3: Backup

```bash
# Create timestamped backup directory
BACKUP_DIR="migration_backups/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"

# Backup files
while read file; do
    cp "$file" "$BACKUP_DIR/"
done < migration_batch1.txt

echo "Backed up to: $BACKUP_DIR"
```

---

### Phase 2: Automated Migration (1-2 minutes)

#### Step 2.1: Dry Run (Optional but Recommended)

```bash
# Preview changes without modifying files
simple migrate --fix-sspec-docstrings --dry-run \
  simple/std_lib/test/features/codegen/cranelift_spec.spl

# Output:
# DRY RUN: Previewing SSpec docstring migration for 1 file(s)...
#   ⚠  cranelift_spec.spl (would be modified)
# DRY RUN complete!
```

**Review Output:**
- Check "Would modify" count
- Verify no errors
- Spot-check one file if concerned

#### Step 2.2: Execute Migration

```bash
# Run migration on single file
simple migrate --fix-sspec-docstrings \
  simple/std_lib/test/features/codegen/cranelift_spec.spl

# Or on multiple files
simple migrate --fix-sspec-docstrings \
  simple/std_lib/test/features/codegen/cranelift_spec.spl \
  simple/std_lib/test/features/ml/config_system_spec.spl \
  simple/std_lib/test/features/language/imports_spec.spl
```

**Expected Output:**
```
Migrating 3 SSpec test file(s) to intensive docstring format...
  ✓  cranelift_spec.spl
  ✓  config_system_spec.spl
  ✓  imports_spec.spl

Migration complete!
  Modified: 3
  Already correct: 0
  Errors: 0

⚠  IMPORTANT: Review all changes before committing!
```

#### Step 2.3: Spot Check

```bash
# Quick visual inspection
git diff simple/std_lib/test/features/codegen/cranelift_spec.spl | head -100

# Check for expected changes:
# - print('describe...') → describe "...":
# - Docstring placeholders added
# - Manual tracking removed
# - Banner prints removed
```

---

### Phase 3: Manual Assertion Conversion (30-60 min/file)

#### Step 3.1: Identify Empty If/Else Blocks

**What to Look For:**
```simple
if result == expected:
else:
```

**Find Them:**
```bash
# Use editor search or:
grep -n "^if.*:$" cranelift_spec.spl | grep -A 1 "^else:"
```

#### Step 3.2: Convert to expect() Syntax

**Pattern Reference:**
| Original | Converted |
|----------|-----------|
| `if x == y:` | `expect(x).to(eq(y))` |
| `if x > y:` | `expect(x).to(be_greater_than(y))` |
| `if flag:` | `expect(flag).to(be_true())` |
| `if list.contains(x):` | `expect(list).to(contain(x))` |

**Example Conversion:**
```simple
# BEFORE (after migration):
val result = compile("fn main(): pass")
if result.is_ok():
else:

# AFTER (manual fix):
val result = compile("fn main(): pass")
expect(result).to(be_ok())
expect(result.unwrap()).to(be_instance_of(CompiledFunction))
```

**Complete Guide:** See `doc/guide/sspec_assertion_conversion.md`

#### Step 3.3: Verify Syntax

```bash
# Test file parses correctly
simple cranelift_spec.spl

# If errors:
# 1. Check for unmatched braces
# 2. Verify expect() syntax
# 3. Look for missing commas
```

---

### Phase 4: Docstring Enhancement (30-60 min/file)

#### Step 4.1: File-Level Docstring

**Replace this:**
```simple
# Cranelift Compilation Specification
```

**With this:**
```simple
"""
# Cranelift Backend Compilation

**Feature ID:** #42
**Category:** Codegen
**Difficulty:** 4/5
**Status:** Complete

## Overview

Tests for the Cranelift JIT compilation backend. Validates that
Simple language constructs compile correctly to native code via
the Cranelift compiler framework.

## Test Coverage

- Function compilation
- Control flow (if/else, match)
- Loops (while, for)
- Recursion handling
- Memory operations

## Implementation

**Files:**
- `src/compiler/src/codegen/cranelift.rs`
- `src/compiler/src/codegen/cranelift/builder.rs`

**Dependencies:**
- Cranelift library (v0.90+)
- LLVM-style IR from MIR

## Related Features

- Feature #3: AST
- Feature #15: MIR
- Feature #43: Interpreter (fallback)
"""
```

**Template:**
- Feature metadata (ID, category, difficulty, status)
- Overview paragraph
- Test coverage list
- Implementation details
- Related features

#### Step 4.2: describe/context/it Docstrings

**Replace all `TODO: Add documentation here` with:**

**For describe blocks:**
```simple
describe "Function compilation":
    """
    ## Function Compilation

    Tests that simple functions compile to valid native code through
    the Cranelift backend. Validates both pure functions and those
    with side effects.

    **Cranelift Phases:**
    1. MIR → Cranelift IR translation
    2. Optimization passes
    3. Native code generation
    """
```

**For it blocks (use Given/When/Then):**
```simple
        it "compiles simple functions":
            """
            **Given** a simple function definition
            **When** compiled via Cranelift backend
            **Then** produces executable native code

            **Example:**
            ```simple
            fn add(a: i32, b: i32) -> i32:
                return a + b
            ```

            **Expected Behavior:**
            - Generates valid machine code
            - Returns correct result when called
            - No runtime errors
            """
            val code = compile("fn add(a: i32, b: i32) -> i32: return a + b")
            expect(code).to(be_ok())
```

**Guidelines:**
- Be specific and technical
- Include code examples
- Document edge cases
- Cross-reference related tests

#### Step 4.3: Quality Checklist

- [ ] File-level docstring has all metadata
- [ ] Every describe/context has overview
- [ ] Every it has Given/When/Then
- [ ] Code examples are syntactically correct
- [ ] Cross-references are accurate
- [ ] No TODO placeholders remain

---

### Phase 5: Testing & Review (15-30 min/file)

#### Step 5.1: Syntax Validation

```bash
# Run the test file
simple simple/std_lib/test/features/codegen/cranelift_spec.spl

# Expected: File executes without parse errors
# Tests may fail (expected if test logic needs work)
# But syntax should be clean
```

#### Step 5.2: Test Execution

```bash
# Run all tests in file
# (Current Simple test runner behavior)

# Check for:
# - All expect() assertions execute
# - No runtime errors
# - Expected pass/fail results
```

#### Step 5.3: Documentation Generation (Future)

```bash
# Once doc generator is ready:
simple doc-gen simple/std_lib/test/features/codegen/cranelift_spec.spl

# Should produce markdown documentation
# Review for formatting and completeness
```

#### Step 5.4: Peer Review

**Checklist for Reviewer:**
- [ ] All assertions converted (no empty if/else)
- [ ] Docstrings are comprehensive
- [ ] Given/When/Then is clear
- [ ] Code examples work
- [ ] File runs without errors
- [ ] Documentation quality is high

**Review Process:**
1. Assignee creates PR with migration
2. Reviewer checks file-by-file
3. Feedback on docstring quality
4. Approve when ready

---

## Common Issues & Solutions

### Issue 1: Parse Errors After Migration

**Symptom:**
```
error: parse error: Unexpected token: expected Indent, found Else
```

**Cause:** Empty if/else block not converted

**Solution:**
```simple
# Find the line number from error
# Replace empty if/else with expect()

# WRONG:
if x == y:
else:

# RIGHT:
expect(x).to(eq(y))
```

### Issue 2: Incorrect Block Types

**Symptom:** Nesting looks wrong

**Cause:** May have hit edge case in pattern matching

**Solution:**
- Check if BDD keyword appears in test description
- Manually fix block type
- Report edge case for tool improvement

### Issue 3: Missing Docstrings

**Symptom:** File has TODO placeholders

**Cause:** Forgot to fill them in

**Solution:** Go through file systematically, replace all TODOs

### Issue 4: Tests Fail After Migration

**Symptom:** Tests that passed before now fail

**Cause:** Assertion conversion changed logic

**Solution:**
- Review original test logic
- Ensure expect() assertions are equivalent
- May need to adjust expected values

---

## Batch Migration Strategy

### Recommended Batches

**Batch 1:** Smallest 10 files (warmup)
- Learn the workflow
- Validate tooling
- Build confidence

**Batch 2:** Medium 20 files (scale up)
- Distribute across team
- Parallel work
- Refine templates

**Batch 3:** Remaining 37 files (finish)
- Full team engagement
- Quality focus
- Documentation polish

### Team Distribution

**3 Developers:**
- Developer 1: 22 files
- Developer 2: 22 files
- Developer 3: 23 files

**Recommended Pairing:**
- Each dev picks category (language, types, infrastructure, etc.)
- Maintain context within category
- Cross-review other categories

### Progress Tracking

```bash
# Create tracking sheet
echo "File,Status,Migrated,Assertions,Docstrings,Tested,Reviewed" > progress.csv

# Update after each file
echo "cranelift_spec.spl,DONE,✓,✓,✓,✓,✓" >> progress.csv
```

**Status Values:**
- TODO: Not started
- MIGRATED: Auto-migration done
- ASSERTIONS: Manual conversion done
- DOCSTRINGS: Documentation complete
- TESTING: Syntax validated
- REVIEWED: Peer reviewed
- DONE: Ready to merge

---

## Quality Standards

### Minimum Requirements

**For Merge Approval:**
- ✅ All assertions converted to expect()
- ✅ No syntax errors
- ✅ All TODO placeholders filled
- ✅ File-level docstring present
- ✅ Peer review complete

### Excellence Standards

**For High-Quality Migration:**
- ✅ Comprehensive file-level metadata
- ✅ Given/When/Then for all tests
- ✅ Code examples in docstrings
- ✅ Cross-references to related features
- ✅ Edge cases documented
- ✅ Implementation details noted

---

## Time Estimates

### Per File (Average)

| Phase | Time | Cumulative |
|-------|------|------------|
| Automated migration | 1 min | 1 min |
| Assertion conversion | 40 min | 41 min |
| Docstring enhancement | 50 min | 91 min |
| Testing & review | 20 min | 111 min |
| **Total** | **~2 hours** | - |

### For 67 Files

| Metric | Estimate |
|--------|----------|
| Automated (67 × 1 min) | 67 minutes |
| Manual work (67 × 90 min) | 100 hours |
| Review (67 × 20 min) | 22 hours |
| **Total** | **~125 hours** |

**With 3 Developers:** ~6 weeks at 2 hours/day each

---

## Tips & Best Practices

### Do's ✅

- **Start small:** Begin with smallest files
- **Use templates:** Copy from pilot_conversion_example.spl
- **Commit often:** One file per commit
- **Ask questions:** Better to clarify than guess
- **Review others:** Learn from different approaches
- **Document issues:** Help improve the tool

### Don'ts ❌

- **Don't rush:** Quality over speed
- **Don't skip testing:** Always run the file
- **Don't leave TODOs:** Fill all placeholders
- **Don't work in silos:** Communicate with team
- **Don't ignore errors:** Fix syntax issues immediately
- **Don't commit broken code:** Tests should at least parse

---

## Troubleshooting

### Getting Help

**Resources:**
1. This guide: `doc/guide/sspec_bulk_migration_workflow.md`
2. Assertion guide: `doc/guide/sspec_assertion_conversion.md`
3. Example file: `pilot_conversion_example.spl`
4. Bug reports: `doc/report/sspec_bug_fix_summary.md`

**Communication:**
- Slack: #sspec-migration
- Issues: Tag with `sspec-migration`
- Office hours: Daily standup

### Reporting Issues

**If you find a bug in the tool:**
1. Document the issue with example
2. Create GitHub issue with `migration-tool` label
3. Include: file name, expected behavior, actual behavior
4. Continue with manual fix for now
5. Tool will be improved for future batches

---

## Appendix

### File List by Size

```bash
# Generate sorted list
find simple/std_lib/test/features -name "*_spec.spl" -type f \
  -exec sh -c 'if grep -q "print(.describe" "$1" 2>/dev/null; then \
    echo "$(wc -l < "$1") $1"; fi' _ {} \; | sort -n > files_by_size.txt
```

### Migration Commands Reference

```bash
# Dry run single file
simple migrate --fix-sspec-docstrings --dry-run file.spl

# Migrate single file
simple migrate --fix-sspec-docstrings file.spl

# Migrate multiple files
simple migrate --fix-sspec-docstrings file1.spl file2.spl file3.spl

# Migrate directory (all *_spec.spl files)
simple migrate --fix-sspec-docstrings directory/

# Show help
simple migrate --help
```

### Backup & Restore

```bash
# Backup
BACKUP_DIR="backups/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"
cp file.spl "$BACKUP_DIR/"

# Restore
cp "$BACKUP_DIR/file.spl" file.spl

# List backups
ls -la backups/
```

---

**End of Workflow Guide**

**Version:** 1.0
**Last Updated:** 2026-01-12
**Maintainer:** Development Team
**Questions:** #sspec-migration channel
