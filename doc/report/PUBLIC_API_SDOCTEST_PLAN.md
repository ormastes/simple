# Public API & Group-Based SDoctest Requirements
**Date:** 2026-02-14
**Enhancement:** Refined documentation coverage rules

---

## Requirements

### 1. Public API Definition
**Source:** Top-most `__init__.spl` file (module entry point)

**Rule:** Only items exported in `__init__.spl` are considered public API

**Example:**
```simple
# src/lib/string/__init__.spl
export trim, split, join, to_upper, to_lower
export StringHelper
export NL, CR, CRLF  # Constants group

# Public API = 8 items (5 functions, 1 class, 3 constants)
# Private = all other items in src/lib/string/*.spl
```

### 2. Group-Based SDoctest Rule
**Rule:** Grouped items need only ONE sdoctest for the entire group

**Detection:** Use existing `group_comment_detection.spl` logic

**Example:**
```simple
# String constants - ONE sdoctest covers all three
export NL, CR, CRLF

# Only one sdoctest needed:
"""
Example: Line endings
  val unix = NL      # "\n"
  val windows = CRLF # "\r\n"
"""
```

### 3. Individual SDoctest Rule
**Rule:** Non-grouped public items each need their own sdoctest

**Example:**
```simple
export trim  # Needs sdoctest
export split # Needs sdoctest (separate from trim)

# NOT a group - different purposes, separated by blank lines
```

---

## Implementation Plan

### Phase 1: __init__.spl Parser (1 hour)
**File:** `src/app/doc_coverage/analysis/init_parser.spl`

**Functions:**
```simple
fn find_module_init(module_path: text) -> text?
  # Find __init__.spl in module directory
  # Returns: path to __init__.spl or nil

fn parse_init_exports(init_path: text) -> [text]
  # Parse "export" statements
  # Returns: list of exported names
  # Handles: export foo, bar, baz

fn get_public_api(module_path: text) -> [text]
  # Combined: find init + parse exports
  # Returns: list of public API item names
```

**Test:** `test/unit/app/doc_coverage/init_parser_spec.spl`

---

### Phase 2: Group Detection Integration (1 hour)
**File:** `src/app/doc_coverage/analysis/group_sdoctest.spl`

**Functions:**
```simple
fn detect_export_groups(exports: [text], items: [DocItem]) -> [ItemGroup]
  # Identify which exported items form groups
  # Uses: existing group_comment_detection.spl logic
  # Returns: list of groups with member items

struct ItemGroup:
  comment: text
  items: [DocItem]
  has_sdoctest: bool
  line_start: i64
  line_end: i64

fn check_group_sdoctest(group: ItemGroup, sdoctest_blocks: [SDocBlock]) -> bool
  # Check if ANY item in group has sdoctest
  # Returns: true if group covered
```

**Test:** `test/unit/app/doc_coverage/group_sdoctest_spec.spl`

---

### Phase 3: Coverage Rule Engine (1.5 hours)
**File:** `src/app/doc_coverage/analysis/coverage_rules.spl`

**Functions:**
```simple
fn compute_public_api_coverage(module_path: text) -> CoverageReport
  # Main entry point
  # Steps:
  #   1. Find __init__.spl
  #   2. Parse exports
  #   3. Detect groups
  #   4. Check sdoctest for each group/item
  #   5. Generate report

struct CoverageReport:
  module: text
  total_public: i64
  groups: [GroupCoverage]
  individual_items: [ItemCoverage]
  overall_coverage: f64

struct GroupCoverage:
  name: text
  items: [text]
  has_sdoctest: bool
  sdoctest_location: text?

struct ItemCoverage:
  name: text
  has_sdoctest: bool
  sdoctest_location: text?
```

**Test:** `test/unit/app/doc_coverage/coverage_rules_spec.spl`

---

### Phase 4: CLI Integration (30 min)
**Update:** `src/app/cli/doc_coverage_command.spl`

**New Flags:**
```bash
--public-api-only     # Only check items in __init__.spl exports
--group-aware         # Apply group sdoctest rule (default: true)
--strict              # Require sdoctest for ALL items (ignore groups)
```

**Example:**
```bash
# Check public API coverage with group awareness
bin/simple doc-coverage --public-api-only src/lib/string/

# Output:
# Public API Coverage (src/lib/string/)
#   Groups: 2/2 (100%)
#     - String constants (NL, CR, CRLF) ✅ sdoctest at doc/guide/string.md:45
#     - Case conversion (to_upper, to_lower) ✅ sdoctest at doc/guide/string.md:78
#   Individual: 3/5 (60%)
#     ✅ trim - sdoctest at doc/guide/string.md:12
#     ✅ split - sdoctest at doc/guide/string.md:23
#     ✅ join - sdoctest at doc/guide/string.md:34
#     ❌ starts_with - missing sdoctest
#     ❌ ends_with - missing sdoctest
#   Overall: 80% (8/10 items covered)
```

---

### Phase 5: Stats Integration (30 min)
**Update:** `src/app/stats/dynamic.spl`

**New Metrics:**
```simple
fn compute_public_api_stats() -> (i64, i64, i64, i64):
  # Returns: (total_public, total_groups, groups_covered, items_covered)

  # Iterate all modules with __init__.spl
  # Aggregate coverage across project
```

**Example Output:**
```bash
$ bin/simple stats

Public API Coverage:
  Total Modules:       12
  Total Public Items:  145
  Groups:              8 (8 covered, 100%)
  Individual:          137 (98 covered, 71%)
  Overall:             106/145 (73%)
```

---

## Examples

### Example 1: Standard Library Module

**File Structure:**
```
src/lib/string/
├── __init__.spl           # Public API definition
├── core.spl               # Core string functions
├── transform.spl          # Transformations
└── constants.spl          # String constants
```

**__init__.spl:**
```simple
# String module public API
use string.core.{trim, split, join, replace, substring}
use string.transform.{to_upper, to_lower, to_title}
use string.constants.{NL, CR, CRLF, TAB, SPACE}

# Public API (13 items)
export trim, split, join, replace, substring
export to_upper, to_lower, to_title
export NL, CR, CRLF, TAB, SPACE
```

**Group Detection:**
```
Group 1: "Core string operations"
  - trim, split, join, replace, substring (5 items)
  - Needs: 1 sdoctest covering the group

Group 2: "Case transformations"
  - to_upper, to_lower, to_title (3 items)
  - Needs: 1 sdoctest covering the group

Group 3: "Whitespace constants"
  - NL, CR, CRLF, TAB, SPACE (5 items)
  - Needs: 1 sdoctest covering the group

Total: 3 groups, 3 sdoctests needed (not 13!)
```

### Example 2: Mixed Public API

**__init__.spl:**
```simple
export parse_json          # Standalone function
export JsonValue           # Standalone type

# Encoding functions (group)
export encode_utf8, encode_utf16, encode_ascii

export JsonError           # Standalone type
```

**Coverage Requirements:**
```
Individual:
  - parse_json: needs sdoctest ✅
  - JsonValue: needs sdoctest ✅
  - JsonError: needs sdoctest ✅

Group:
  - Encoding functions (encode_utf8, encode_utf16, encode_ascii)
    Needs: 1 sdoctest for the group ✅

Total: 4 sdoctests needed (not 7)
```

---

## Migration Path

### Backward Compatibility
```bash
# Old behavior (all public items)
bin/simple doc-coverage src/

# New behavior (only __init__.spl exports)
bin/simple doc-coverage --public-api-only src/

# Group-aware (default)
bin/simple doc-coverage --public-api-only --group-aware src/

# Strict (every item needs sdoctest)
bin/simple doc-coverage --public-api-only --strict src/
```

### Suggested Workflow
1. **Phase 1:** Run `--public-api-only` to see what's actually public
2. **Phase 2:** Run `--group-aware` to see optimized requirements
3. **Phase 3:** Add group sdoctests first (covers multiple items)
4. **Phase 4:** Add individual sdoctests for remaining items

---

## Benefits

### 1. **Reduced Documentation Burden**
- Group sdoctest: 1 example covers 5+ constants
- Focus: Public API only (not internal helpers)
- Result: ~60-70% fewer required sdoctests

### 2. **Better Documentation Quality**
- Group examples show relationships
- Public API clearly defined
- Internal code can have inline comments instead

### 3. **Realistic Coverage Goals**
- 100% public API coverage achievable
- Groups make large constant sets manageable
- Prioritizes user-facing documentation

---

## Implementation Estimate

**Total Time:** 4.5 hours

| Phase | Time | Agent |
|-------|------|-------|
| 1. __init__.spl parser | 1h | general-purpose |
| 2. Group detection | 1h | general-purpose |
| 3. Coverage rules | 1.5h | general-purpose |
| 4. CLI integration | 0.5h | general-purpose |
| 5. Stats integration | 0.5h | general-purpose |

**Tests:** 3 new spec files (~300 lines total)

---

## Verification

### Test Cases

**Test 1: Simple Module**
```
src/lib/math/__init__.spl:
  export abs, sqrt, pow

Expected:
  - 3 individual items (no groups detected)
  - 3 sdoctests required
```

**Test 2: Grouped Constants**
```
src/lib/http/__init__.spl:
  export GET, POST, PUT, DELETE, PATCH

Expected:
  - 1 group (HTTP methods)
  - 1 sdoctest required
```

**Test 3: Mixed**
```
src/lib/json/__init__.spl:
  export parse, stringify
  export JsonValue, JsonError

Expected:
  - 1 group (parse, stringify - related functions)
  - 2 individual (JsonValue, JsonError - types)
  - 3 sdoctests required
```

---

## Next Steps

1. **User Approval:** Confirm this design matches requirements
2. **Spawn Agents:** Implement 5 phases in parallel where possible
3. **Testing:** Verify on real modules (std, core, app)
4. **Documentation:** Update user guide with new rules
5. **Migration:** Add examples for existing modules

---

**Status:** Ready for implementation
**Estimated Completion:** 4.5 hours
