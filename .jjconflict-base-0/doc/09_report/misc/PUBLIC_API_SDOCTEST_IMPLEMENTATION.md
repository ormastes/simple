# Public API SDoctest Requirements - Implementation Summary

## Overview

Enhanced the documentation coverage system to enforce SDoctest requirements for public APIs documented in `__init__.spl` files.

## Rules Implemented

1. **Grouped Items** (under comment headers): At least ONE SDoctest for the entire group
2. **Non-grouped Items**: EACH item needs its own SDoctest

## Architecture

### 1. Init Parser (`src/app/doc_coverage/analysis/init_parser.spl`)

**Purpose**: Parse `__init__.spl` files to extract public API documentation

**Key Types**:
```simple
struct PublicApiGroup:
    group_name: text          # e.g., "File operations"
    group_line: i64           # Line number in __init__.spl
    items: [text]             # Function names in group
    has_group_sdoctest: bool  # Coverage status
    file_path: text           # Path to __init__.spl

struct PublicApiItem:
    name: text                # Function name
    line: i64                 # Line number
    file_path: text
    is_grouped: bool
    group_name: text
    has_sdoctest: bool        # Coverage status
```

**Main Functions**:
- `parse_init_file(file_path: text) -> ([PublicApiGroup], [PublicApiItem])`
  - Parses __init__.spl files
  - Returns (groups, ungrouped_items)
  - Supports comment-based API docs

**Detection Patterns**:

1. **Group Headers** (capital letter, no dash):
   ```
   # File operations
   # Public API Groups:
   ```

2. **Group Items** (dash syntax):
   ```
   #   - file_read
   # - file_write
   ```

3. **Use Statements**:
   ```
   use std.spec.{describe, it, expect}
   ```

### 2. Group SDoctest (`src/app/doc_coverage/analysis/group_sdoctest.spl`)

**Purpose**: Match exports to groups and check SDoctest coverage

**Key Types**:
```simple
struct ItemGroup:
    comment: text           # Group comment text
    items: [text]          # Item names in group
    has_sdoctest: bool     # Whether group has sdoctest
    line_start: i64
    line_end: i64

struct GroupDetectionResult:
    groups: [ItemGroup]
    individual_items: [text]  # Items not in any group
```

**Main Functions**:
- `detect_export_groups(exports: [text], source_path: text) -> GroupDetectionResult`
  - Groups consecutive exports
  - Detects group comments
  
- `check_group_sdoctest(group: ItemGroup, sdoctest_blocks: [text]) -> bool`
  - Checks if ANY item in group has SDoctest
  
- `enhance_groups_with_sdoctest(groups: [ItemGroup], sdoctest_blocks: [text]) -> [ItemGroup]`
  - Updates groups with coverage status

### 3. Integration Point

The analysis module (`src/app/doc_coverage/analysis/mod.spl`) re-exports:
- `PublicApiGroup`, `PublicApiItem` from init_parser
- `ItemGroup`, `GroupDetectionResult` from group_sdoctest
- All related functions

## Example __init__.spl Format

```simple
# Spec Module - Testing Framework
#
# SSpec testing framework for BDD.
#
# Public API:
#   - use std.spec.{describe, it, expect}
#   - use std.spec.{before, after, before_each, after_each}
#   - use std.spec.decorators.{skip_it, pending_it}
#
# Example:
#   describe "Calculator":
#     it "adds numbers":
#       expect(2 + 2).to_equal(4)
```

## Usage Example

```simple
use doc_coverage.analysis.init_parser.{parse_init_file}
use app.doc_coverage.analysis.sdoctest_coverage.{load_sdoctest_blocks}

# Parse public API from __init__.spl
val result = parse_init_file("src/lib/spec/__init__.spl")
val groups = result.0
val items = result.1

# Load SDoctest blocks from documentation
val sdoctest_blocks = load_sdoctest_blocks()

# Check coverage
for group in groups:
    val has_test = check_group_sdoctest(group, sdoctest_blocks)
    if not has_test:
        print "WARNING: Group '{group.group_name}' missing SDoctest"

for item in items:
    # Each ungrouped item needs its own test
    # (Implementation in sdoctest_coverage.spl)
```

## Test Coverage

Location: `test/unit/app/doc_coverage/init_parser_spec.spl`

Tests:
1. Parse real `__init__.spl` files
2. Detect group headers
3. Extract item names
4. Handle use statements
5. Return empty for non-existent files

## Next Steps (Optional Enhancements)

1. **CLI Integration**: Add `--enforce-public-sdoctest` flag to compiler
2. **Warning Generation**: Emit warnings for missing coverage
3. **Coverage Reports**: Include public API coverage in `bin/simple doc-coverage`
4. **Threshold System**: Set minimum coverage % for public APIs
5. **Auto-Tag Generation**: Generate `@tag:api` for documented items

## Files Modified

1. `src/app/doc_coverage/analysis/init_parser.spl` - Enhanced parser (282 lines)
2. `src/app/doc_coverage/analysis/mod.spl` - Added exports
3. `test/lib/doc_coverage` - Symlink for testing
4. `test/unit/app/doc_coverage/init_parser_spec.spl` - Tests

## Existing Infrastructure

The implementation leverages existing infrastructure:
- `sdoctest_coverage.spl` - SDoctest extraction and matching
- `group_comment_detection.spl` - Variable group detection patterns
- `export_parser.spl` - Export statement parsing
- `group_sdoctest.spl` - Group-based coverage checking

All components integrate seamlessly with the existing doc coverage system.
