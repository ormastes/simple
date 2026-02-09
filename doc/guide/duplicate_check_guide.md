# Code Duplication Detection Guide

## Overview

The Simple language compiler includes a built-in code duplication detector that helps identify duplicate code blocks across your codebase. This tool uses a Karp-Rabin rolling hash algorithm with token-based analysis to find structural duplicates efficiently.

## Quick Start

### Basic Usage

```bash
# Scan entire src/ directory
simple duplicate-check src/

# Scan specific directory
simple duplicate-check src/app/

# Scan single file
simple duplicate-check src/app/main.spl
```

### Build System Integration

```bash
# Run duplication check as part of build
simple build duplication

# Include in quality checks
simple build check
```

## Configuration

### Config File

Create `simple.duplicate-check.sdn` in your project root:

```sdn
duplicate-check:
  # Detection thresholds
  min-tokens: 30              # Minimum tokens per duplicate block
  min-lines: 5                # Minimum lines per duplicate block
  min-impact: 100             # Minimum impact score (occurrences × lines)

  # Normalizations
  ignore-identifiers: true    # Treat all identifiers as IDENTIFIER
  ignore-literals: false      # Keep literal values distinct
  ignore-comments: true       # Skip comments in comparison
  ignore-whitespace: true     # Normalize whitespace

  # Reporting
  output-format: text         # text | json | sdn
  report-path: doc/analysis/duplicate_db.sdn
  max-allowed: 0              # Fail build if > N duplicates

  # Exclusions
  exclude:
    - "test/"                 # Exclude test directories
    - "doc/"                  # Exclude documentation
    - "**/*_spec.spl"         # Exclude spec files
    - "**/*_test.spl"         # Exclude test files

  # Advanced (experimental)
  use-ast-features: false
  use-cosine-similarity: false
```

### Command-Line Options

```bash
# Adjust thresholds
simple duplicate-check src/ --min-tokens=20 --min-lines=3

# Change impact filter
simple duplicate-check src/ --min-impact=50

# Output formats
simple duplicate-check src/ --format=json
simple duplicate-check src/ --format=sdn

# Add exclusions
simple duplicate-check src/ --exclude="vendor/"
simple duplicate-check src/ --exclude="generated/"
```

## Understanding Results

### Text Output

```
Duplication Analysis Report
===========================

Found 3 duplicate groups (142 total lines duplicated)

1. Impact Score: 140 (5 occurrences, 28 lines each)
   Files:
   - src/app/ffi_gen/specs/cranelift_ops.spl:34-42
   - src/app/ffi_gen/specs/cranelift_ops.spl:50-58
   - src/app/ffi_gen/specs/cranelift_advanced.spl:25-33
   - src/app/ffi_gen/specs/cranelift_advanced.spl:45-53
   - src/app/ffi_gen/specs/cranelift_codegen.spl:207-215

   Code preview:
      let mut contexts = FUNC_CONTEXTS.lock().unwrap();
      if let Some(fctx) = contexts.get_mut(&ctx) {
      ...

Summary:
- Total duplicate groups: 3
- Total occurrences: 12
- Total lines duplicated: 142
- Files affected: 8
```

### Impact Score

**Impact Score = Occurrences × Lines per Block**

- Higher scores indicate more significant duplication
- Focus on high-impact duplicates first
- Use `--min-impact` to filter noise

### JSON Output

```bash
simple duplicate-check src/ --format=json > duplicates.json
```

```json
{
  "summary": {
    "total_groups": 3,
    "total_occurrences": 12,
    "total_lines": 142,
    "files_affected": 8
  },
  "duplicates": [
    {
      "group_id": 1,
      "occurrences": 5,
      "lines_per_block": 28,
      "impact_score": 140,
      "blocks": [...]
    }
  ]
}
```

### SDN Database

```bash
simple duplicate-check src/ --format=sdn
```

Creates `doc/analysis/duplicate_db.sdn`:

```sdn
metadata:
  total_groups: 3
  total_lines: 142

duplicate_groups |group_id, occurrences, lines, impact|
  1, 5, 28, 140
  2, 2, 11, 22
  3, 3, 8, 24

duplicate_blocks |group_id, file, line_start, line_end, hash|
  1, src/app/ffi_gen/specs/cranelift_ops.spl, 34, 42, abc123
  1, src/app/ffi_gen/specs/cranelift_ops.spl, 50, 58, abc123
  ...
```

## Detection Algorithm

### Token-Based Matching

The duplicate detector uses token-level comparison instead of line-based comparison:

1. **Tokenize** - Convert source code to tokens (keywords, identifiers, operators, literals)
2. **Normalize** - Apply configured normalizations (identifiers, literals, whitespace)
3. **Hash** - Compute rolling hashes over token windows
4. **Match** - Find identical hash sequences across files
5. **Group** - Group matching blocks by hash
6. **Rank** - Sort by impact score (occurrences × lines)

### Why Token-Based?

- **Structure-aware** - Matches code structure, not formatting
- **Normalization** - Can ignore variable names (`ignore-identifiers`)
- **Language-specific** - Understands Simple syntax
- **Efficient** - Rolling hash is O(n) complexity

### Example

```simple
# Original code
fn process_user(user_id):
    val user = fetch_user(user_id)
    val data = transform(user)
    return save_result(data)

# Duplicate (detected with ignore-identifiers: true)
fn handle_item(item_id):
    val item = fetch_item(item_id)
    val result = transform(item)
    return save_result(result)
```

With `ignore-identifiers: true`, these are detected as duplicates because:
- Token sequence: `fn`, `IDENTIFIER`, `(`, `IDENTIFIER`, `)`, `:`, ...
- Structural similarity: same control flow, same function calls

## Best Practices

### 1. Start with High Thresholds

```sdn
min-tokens: 30       # Only large duplicates
min-lines: 5         # At least 5 lines
min-impact: 100      # High-impact only
```

This reduces noise and focuses on significant duplicates.

### 2. Use Identifier Normalization

```sdn
ignore-identifiers: true
```

This finds structural duplicates regardless of variable naming.

### 3. Exclude Test Code

```sdn
exclude:
  - "test/"
  - "**/*_spec.spl"
  - "**/*_test.spl"
```

Test code often has intentional duplication (fixtures, setup, assertions).

### 4. Track Over Time

```bash
# Generate baseline
simple duplicate-check src/ --format=sdn

# Track in version control
git add doc/analysis/duplicate_db.sdn

# Compare in CI/CD
simple duplicate-check src/ --max-allowed=10
```

### 5. Refactor Incrementally

Don't try to fix all duplicates at once:

1. Start with highest impact scores
2. Extract common code to helper functions
3. Create shared modules for repeated patterns
4. Document intentional duplicates (if any)

## Integration with CI/CD

### GitHub Actions

```yaml
- name: Check Code Duplication
  run: |
    bin/simple duplicate-check src/ --format=json > duplicates.json
    bin/simple duplicate-check src/ --max-allowed=5
```

### Build Failure

Set `max-allowed` to fail builds:

```sdn
max-allowed: 5     # Fail if more than 5 duplicate groups
fail-on-duplicates: true
```

```bash
simple build duplication
# Exit code 1 if duplicates > max-allowed
```

## Troubleshooting

### Slow Performance

The duplicate checker scans all files character-by-character, which can be slow for large codebases.

**Solutions:**
- Use exclusion patterns to skip non-source files
- Increase `min-tokens` to reduce hash collisions
- Run only on changed files in CI/CD

### False Positives

Small code patterns may match accidentally.

**Solutions:**
- Increase `min-tokens` (default: 30)
- Increase `min-lines` (default: 5)
- Use `ignore-identifiers: false` for stricter matching

### False Negatives

Duplicates not detected.

**Solutions:**
- Enable `ignore-identifiers: true` to find structural duplicates
- Enable `ignore-literals: true` to ignore constant differences
- Lower `min-impact` threshold

### No Matches Found

The detector found potential blocks but no matching groups.

**Causes:**
- Thresholds too strict (`min-impact` too high)
- Hash window alignment issues
- Code blocks too short

## Advanced Features (Experimental)

### AST-Based Features

```sdn
use-ast-features: true
```

Extracts structural features from AST:
- Statement types (if/while/for/match)
- Nesting depth
- Control flow patterns

### Cosine Similarity

```sdn
use-cosine-similarity: true
similarity-threshold: 0.85
```

Uses TF-IDF weighted feature vectors for fuzzy matching.

**Note:** These features are experimental and may not work in all cases.

## Examples

### Basic Scan

```bash
simple duplicate-check src/
```

### CI/CD Integration

```bash
# Fail on any duplicates
simple duplicate-check src/ --max-allowed=0

# Allow some duplicates
simple duplicate-check src/ --max-allowed=5 --min-impact=150
```

### Focus on High-Impact

```bash
# Only show duplicates with impact > 200
simple duplicate-check src/ --min-impact=200

# Large blocks only
simple duplicate-check src/ --min-tokens=50 --min-lines=10
```

### JSON for Tooling

```bash
# Export to JSON
simple duplicate-check src/ --format=json > report.json

# Process with jq
simple duplicate-check src/ --format=json | jq '.summary.total_groups'
```

## Related Commands

- `simple lint` - Code quality linting
- `simple fmt` - Code formatting
- `simple build check` - All quality checks (includes duplication)
- `simple build duplication` - Run duplication check via build system

## Further Reading

- [Karp-Rabin Algorithm](https://en.wikipedia.org/wiki/Rabin%E2%80%93Karp_algorithm)
- [CPD (Copy/Paste Detector)](https://pmd.github.io/latest/pmd_userdocs_cpd.html)
- [Code Clone Detection](https://en.wikipedia.org/wiki/Duplicate_code)
