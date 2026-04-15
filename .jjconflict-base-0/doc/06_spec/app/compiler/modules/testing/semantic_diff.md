# Semantic Diff Tool Specification (#889)

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** High  
**Difficulty:** 4

## Overview

Semantic diff tool that compares code at the AST/IR level rather than text level, showing meaningful changes while ignoring whitespace, comments, and formatting differences. Makes LLM output changes reviewable and understandable.

## Motivation

**Problem:** Traditional text diffs show:
- Formatting changes as significant
- Reordered functions/imports as complete rewrites
- Refactored code with same semantics as different
- Noise from comments, whitespace, style

**Solution:** Semantic diff shows only:
- Added/removed/changed functions
- Type signature changes
- Control flow modifications
- Semantic behavior differences

## Features

### Core Functionality

**Basic Command:**
```bash
simple diff --semantic old.spl new.spl
simple diff --semantic old.spl new.spl --format=json
simple diff --semantic --git HEAD~1 HEAD file.spl
```

**Output Formats:**
- Human-readable (colored terminal)
- JSON (for LLM tools)
- HTML (for web review)
- Unified diff (git-compatible)

### Diff Categories

**1. Function Changes**
```
Function: calculate_tax
  Status: Modified
  Changes:
    - Parameter added: discount: f64
    - Return type: i64 → Result<i64, TaxError>
    - Body: 3 statements added, 1 removed
```

**2. Type Changes**
```
Struct: User
  Status: Modified
  Changes:
    + Field added: email_verified: bool
    - Field removed: legacy_id: i64
    ~ Field modified: age: i32 → Option<i32>
```

**3. Import/Dependency Changes**
```
Imports:
  + use crypto.hash
  - use old_api.auth
  ~ use http.client → use http.client.v2
```

**4. Signature Changes Only**
```
Function: process_order
  Signature changed, body unchanged:
    - process_order(order: Order)
    + process_order(order: Order, options: ProcessOptions)
```

**5. Refactoring Detection**
```
Function: validate_input
  Refactored: body restructured, semantics unchanged
  Confidence: 95%
  Details: Extracted helper function validate_format
```

### Advanced Features

**Ignore Options:**
```bash
# Ignore whitespace and formatting
simple diff --semantic --ignore-formatting old.spl new.spl

# Ignore comments
simple diff --semantic --ignore-comments old.spl new.spl

# Ignore reordering
simple diff --semantic --ignore-order old.spl new.spl

# Show only signature changes
simple diff --semantic --signatures-only old.spl new.spl
```

**Confidence Levels:**
```
Changes with confidence scores:
  Function add_user: Modified (confidence: 100%)
  Function calculate_total: Refactored (confidence: 85%)
  Function format_date: Unknown change (confidence: 60%)
```

**Change Impact:**
```
Impact Analysis:
  Breaking changes: 2
    - User.age type changed (affects 5 call sites)
    - calculate_tax now returns Result (affects 12 callers)
  
  Non-breaking changes: 7
    - New optional parameters (backwards compatible)
    - Internal refactoring (no API change)
```

## Implementation

### Architecture

```
┌────────────────┐
│  Input Files   │
│  old.spl       │
│  new.spl       │
└────────┬───────┘
         │
         ▼
┌────────────────┐
│  Parser        │ → AST for both files
└────────┬───────┘
         │
         ▼
┌────────────────┐
│  Normalizer    │ → Remove formatting, sort
└────────┬───────┘
         │
         ▼
┌────────────────┐
│  AST Differ    │ → Compare structures
└────────┬───────┘
         │
         ▼
┌────────────────┐
│  Semantic      │ → Classify changes
│  Analyzer      │
└────────┬───────┘
         │
         ▼
┌────────────────┐
│  Formatter     │ → Output (text/JSON/HTML)
└────────────────┘
```

### Diffing Algorithm

**Phase 1: Parse & Normalize**
```rust
1. Parse both files to AST
2. Normalize:
   - Remove comments
   - Strip whitespace
   - Sort imports/definitions (if --ignore-order)
   - Canonicalize formatting
```

**Phase 2: Match Elements**
```rust
1. Build symbol tables for both files
2. Match by name and signature
3. Identify:
   - Unchanged (identical AST)
   - Modified (same name, different body/signature)
   - Added (only in new)
   - Removed (only in old)
   - Renamed (heuristic matching)
```

**Phase 3: Analyze Changes**
```rust
For each modified element:
  1. Compare signatures (params, return type)
  2. Compare body (control flow, statements)
  3. Classify change type:
     - Signature-only change
     - Body-only change
     - Refactoring (same semantics)
     - Breaking change
     - Non-breaking enhancement
```

**Phase 4: Compute Similarity**
```rust
Similarity score (0-100%):
  - AST structure similarity
  - Variable name similarity
  - Control flow similarity
  - Expression similarity
  
If similarity > 90%: "Refactored"
If similarity > 70%: "Modified (minor)"
If similarity < 70%: "Modified (major)"
```

### JSON Output Format

```json
{
  "files": {
    "old": "old.spl",
    "new": "new.spl"
  },
  "summary": {
    "functions_added": 2,
    "functions_removed": 1,
    "functions_modified": 5,
    "types_added": 1,
    "types_modified": 2,
    "breaking_changes": 2
  },
  "changes": [
    {
      "type": "function",
      "name": "calculate_tax",
      "status": "modified",
      "changes": {
        "signature": {
          "parameters": {
            "added": [{"name": "discount", "type": "f64"}],
            "removed": [],
            "modified": []
          },
          "return_type": {
            "old": "i64",
            "new": "Result<i64, TaxError>"
          }
        },
        "body": {
          "statements_added": 3,
          "statements_removed": 1,
          "similarity": 85.0
        }
      },
      "impact": {
        "breaking": true,
        "affected_callers": 12
      }
    }
  ]
}
```

## Use Cases

### 1. Code Review
```bash
# Show semantic changes in PR
simple diff --semantic main..feature-branch src/

# Export for review tool
simple diff --semantic --format=json main..HEAD > review.json
```

### 2. LLM Output Validation
```bash
# Compare LLM-generated code to original
simple diff --semantic original.spl llm_output.spl

# Check if only formatting changed
simple diff --semantic --signatures-only before.spl after.spl
```

### 3. Refactoring Verification
```bash
# Verify refactoring didn't change semantics
simple diff --semantic --ignore-order old.spl new.spl

# Show only breaking changes
simple diff --semantic --breaking-only old.spl new.spl
```

### 4. API Evolution Tracking
```bash
# Track API changes across versions
simple diff --semantic v1.0/api.spl v2.0/api.spl --impact-analysis

# Generate migration guide
simple diff --semantic --migration-guide v1.0/ v2.0/ > MIGRATION.md
```

### 5. Git Integration
```bash
# Use as git difftool
git config diff.simple.command 'simple diff --semantic'
git diff --tool=simple

# Pre-commit hook
simple diff --semantic --breaking-only HEAD $STAGED_FILE
```

## Benefits for LLM Tools

1. **Meaningful Changes** - Focus on semantic differences, not formatting
2. **Breaking Detection** - Identify changes that break callers
3. **Refactoring Safe** - Verify refactorings preserve semantics
4. **Review Efficiency** - Reduce noise in code reviews
5. **Migration Help** - Generate upgrade guides automatically

## Implementation Plan

### Phase 1: Core Differ (3 days)
- [ ] AST parsing for both files
- [ ] Normalization (formatting, comments, order)
- [ ] Element matching (name-based)
- [ ] Basic diff output (added/removed/modified)

### Phase 2: Semantic Analysis (3 days)
- [ ] Signature comparison
- [ ] Body similarity computation
- [ ] Refactoring detection heuristics
- [ ] Change classification

### Phase 3: Output Formats (2 days)
- [ ] Human-readable terminal output
- [ ] JSON export
- [ ] HTML report generation
- [ ] Git-compatible unified diff

### Phase 4: Impact Analysis (2 days)
- [ ] Breaking change detection
- [ ] Caller analysis
- [ ] Migration guide generation
- [ ] Confidence scoring

### Phase 5: Git Integration (1 day)
- [ ] Git difftool integration
- [ ] Branch comparison
- [ ] Pre-commit hooks
- [ ] CI/CD integration

**Total Estimated Effort:** 11 days

## File Structure

```
src/compiler/src/semantic_diff/
├── mod.rs              # Main entry point
├── parser.rs           # Parse files to AST
├── normalizer.rs       # Normalize AST
├── matcher.rs          # Match elements between files
├── analyzer.rs         # Semantic analysis
├── similarity.rs       # Similarity computation
├── impact.rs           # Breaking change detection
├── formats/
│   ├── human.rs        # Human-readable output
│   ├── json.rs         # JSON export
│   ├── html.rs         # HTML report
│   └── unified.rs      # Git-compatible diff
└── git.rs              # Git integration

src/compiler/src/bin/simple-diff.rs   # Standalone binary

tests/semantic_diff/
├── basic_spec.rs       # Basic diffing tests
├── refactoring_spec.rs # Refactoring detection
├── breaking_spec.rs    # Breaking change tests
└── formats_spec.rs     # Output format tests
```

## Example Outputs

### Human-Readable (Terminal)
```
Semantic diff: old.spl → new.spl

Functions:
  ✓ calculate_tax (unchanged)
  ~ process_order (modified)
    + Parameter: options: ProcessOptions
    ~ Body: 5 statements changed (85% similar)
  + validate_email (added)
  - old_validation (removed)

Types:
  ~ User (modified)
    + Field: email_verified: bool
    - Field: legacy_id: i64

Summary:
  2 functions modified
  1 function added
  1 function removed
  1 type modified
  0 breaking changes
```

### JSON (for LLM tools)
```json
{
  "summary": {"modified": 2, "added": 1, "removed": 1},
  "changes": [
    {
      "type": "function",
      "name": "process_order",
      "status": "modified",
      "similarity": 85.0,
      "breaking": false
    }
  ]
}
```

## Related Features

- #885-887: AST/HIR/MIR export (provides input)
- #914: API surface lock file (similar concept)
- #908-910: Canonical formatter (normalization)

## Success Metrics

- [ ] Detect 100% of breaking changes
- [ ] <5% false positives (refactoring as change)
- [ ] 90%+ developer satisfaction
- [ ] 10x faster code review
- [ ] LLM output validation in <1 second

## References

- **semantic-diff** (GitHub) - Ruby semantic differ
- **difftastic** (Rust) - Structural diff tool
- **ast-diff** (Python) - AST-based diffing
- **Mergiraf** (Rust) - Semantic merge tool

---

**Next Steps:**
1. Review and approve specification
2. Implement Phase 1 (core differ)
3. Test with real codebases
4. Add to feature.md when complete
