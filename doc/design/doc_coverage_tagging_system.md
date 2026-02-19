# Documentation Coverage Tagging System - Design Document

**Status:** Design Complete
**Priority:** High
**Estimated Effort:** 2-3 hours (implementation)
**Target:** Auto-tag functions/modules based on documentation status for filtering and reporting

---

## Overview

This document specifies a comprehensive tagging system for the documentation coverage analysis tool. Tags provide machine-readable metadata about documentation status, enabling filtering, reporting, and threshold enforcement across different scopes of the codebase.

**Key Goals:**
1. **Automatic tag generation** based on analysis results
2. **Consistent naming convention** for all tag categories
3. **Filterable output** for CLI commands and reports
4. **Extensible schema** for future tag categories

---

## Tag Naming Convention

All tags follow a strict naming convention to ensure consistency and machine-parseability:

### Rules
1. **Lowercase only** - No uppercase letters (e.g., `coverage:excellent` not `Coverage:Excellent`)
2. **Underscores for multi-word** - Use `_` to separate words (e.g., `missing_sdoctest` not `missing-sdoctest`)
3. **Colon separator** - Category and value separated by `:` (e.g., `scope:stdlib`)
4. **No spaces** - Tags must be single tokens
5. **Alphanumeric + underscore + colon only** - No special characters except `_` and `:`

### Format
```
<category>:<value>
```

**Examples:**
- `coverage:excellent`
- `doc:missing_sdoctest`
- `scope:stdlib`
- `api:public`
- `group:documented`

---

## Tag Categories

### 1. Coverage Level Tags

**Category:** `coverage`

Auto-generated based on percentage of documentation completeness for an item or file.

| Tag | Threshold | Description |
|-----|-----------|-------------|
| `coverage:excellent` | ≥95% | Nearly complete documentation |
| `coverage:good` | 80-94% | Well-documented, minor gaps |
| `coverage:acceptable` | 60-79% | Adequate documentation |
| `coverage:poor` | 40-59% | Significant gaps |
| `coverage:insufficient` | <40% | Critical documentation needed |
| `coverage:none` | 0% | No documentation present |

**Calculation:**
```
coverage_percent = (documented_items / total_items) * 100

if coverage_percent >= 95:
    tag = "coverage:excellent"
elif coverage_percent >= 80:
    tag = "coverage:good"
elif coverage_percent >= 60:
    tag = "coverage:acceptable"
elif coverage_percent >= 40:
    tag = "coverage:poor"
elif coverage_percent > 0:
    tag = "coverage:insufficient"
else:
    tag = "coverage:none"
```

**Applied to:**
- Individual `DocItem` (function, struct, class, etc.)
- `FileCoverage` (aggregate for entire file)
- `CoverageReport` (overall codebase coverage)

---

### 2. Documentation Status Tags

**Category:** `doc`

Indicates specific documentation issues or completeness.

| Tag | Description | Applied When |
|-----|-------------|--------------|
| `doc:complete` | All required documentation present | Has inline comment + sdoctest (if public function) |
| `doc:incomplete` | Partial documentation | Has inline comment OR sdoctest, but not both |
| `doc:missing_inline_comment` | No inline comment | `has_inline_comment == false` |
| `doc:missing_sdoctest` | Public function lacks sdoctest | `is_public && needs_sdoctest() && !has_sdoctest` |
| `doc:missing_group_comment` | Variable group undocumented | Group detection found undocumented variable cluster |
| `doc:missing_all` | No documentation whatsoever | `!has_inline_comment && !has_docstring && !has_sdoctest` |
| `doc:has_inline` | Has inline comment | `has_inline_comment == true` |
| `doc:has_docstring` | Has docstring | `has_docstring == true` |
| `doc:has_sdoctest` | Has sdoctest | `has_sdoctest == true` |

**Multiple tags:** Items can have multiple `doc:*` tags (e.g., `doc:has_inline` + `doc:missing_sdoctest`)

**Examples:**
```simple
# Function with inline comment but no sdoctest
# Tags: doc:has_inline, doc:missing_sdoctest, doc:incomplete
fn helper(x: i64) -> i64:
    x * 2

# Function with full documentation
# Tags: doc:complete, doc:has_inline, doc:has_sdoctest
fn square(x: i64) -> i64:
    """
    Squares a number.

    Example:
        val result = square(4)
        # result is 16
    """
    x * x
```

---

### 3. Scope Tags

**Category:** `scope`

Auto-generated from file path to indicate which part of the codebase the item belongs to.

| Tag | Path Pattern | Description |
|-----|--------------|-------------|
| `scope:stdlib` | `src/std/**` | Standard library (highest priority for docs) |
| `scope:core` | `src/compiler_core/**` | Core compiler library (high priority) |
| `scope:lib` | `src/lib/**` | Internal libraries (medium priority) |
| `scope:app` | `src/app/**` | Applications/tools (lower priority) |
| `scope:compiler` | `src/compiler/**` | Compiler backend (medium priority) |
| `scope:test` | `test/**` | Test files (documentation optional) |
| `scope:unknown` | Other paths | Unrecognized path |

**Generation logic:**
```simple
fn generate_scope_tag(file_path: text) -> text:
    if file_path.starts_with("src/std/"):
        return "scope:stdlib"
    elif file_path.starts_with("src/compiler_core/"):
        return "scope:core"
    elif file_path.starts_with("src/lib/"):
        return "scope:lib"
    elif file_path.starts_with("src/app/"):
        return "scope:app"
    elif file_path.starts_with("src/compiler/"):
        return "scope:compiler"
    elif file_path.starts_with("test/"):
        return "scope:test"
    else:
        return "scope:unknown"
```

---

### 4. Public API Tags

**Category:** `api`

Indicates whether an item is part of the public API or internal implementation.

| Tag | Description | Detection Method |
|-----|-------------|------------------|
| `api:public` | Exported in `__init__.spl` or `mod.spl` | Export parser finds name in exports |
| `api:internal` | Not exported, internal implementation | Not found in exports |
| `api:exported` | Explicitly exported (alias for `api:public`) | Same as `api:public` |
| `api:private` | Explicitly marked private (future) | Visibility modifier (not yet implemented) |

**Priority:** Public API items require more documentation than internal items.

**Example:**
```simple
# mod.spl
fn public_function():
    # Tags: api:public, doc:missing_sdoctest (if no sdoctest)
    pass

fn _internal_helper():
    # Tags: api:internal (no sdoctest required)
    pass

export public_function
```

---

### 5. Group Comment Tags

**Category:** `group`

Applied to variable groups detected by group comment analysis.

| Tag | Description | Applied When |
|-----|-------------|--------------|
| `group:documented` | Variable group has group comment | Group comment found above variable cluster |
| `group:undocumented` | Variable group lacks group comment | No group comment for 3+ related variables |
| `group:partial` | Some variables in group documented | Mixed documentation in group |

**Example:**
```simple
# Configuration settings (well-documented group)
# Tags: group:documented
val MAX_SIZE = 1024
val MIN_SIZE = 16
val DEFAULT_SIZE = 256

# Undocumented variable group
# Tags: group:undocumented
val cache_size = 100
val cache_ttl = 3600
val cache_enabled = true
```

---

### 6. Item Kind Tags

**Category:** `kind`

Indicates the type of documented item (from `DocKind` enum).

| Tag | Description | DocKind |
|-----|-------------|---------|
| `kind:function` | Function or method | `DocKind.Function` |
| `kind:struct` | Struct definition | `DocKind.Struct` |
| `kind:class` | Class definition | `DocKind.Class` |
| `kind:enum` | Enum definition | `DocKind.Enum` |
| `kind:variant` | Enum variant | `DocKind.EnumVariant` |
| `kind:constant` | Constant value | `DocKind.Constant` |
| `kind:variable` | Variable declaration | `DocKind.Variable` |
| `kind:module` | Module | `DocKind.Module` |
| `kind:impl` | Implementation block | `DocKind.ImplBlock` |

---

### 7. Priority Tags (Derived)

**Category:** `priority`

Derived from combination of scope + API status to indicate documentation priority.

| Tag | Criteria | Description |
|-----|----------|-------------|
| `priority:critical` | `scope:stdlib` + `api:public` | Public stdlib - MUST be documented |
| `priority:high` | `scope:core` + `api:public` OR `scope:lib` + `api:public` | Public core/lib APIs |
| `priority:medium` | `scope:app` + `api:public` OR any `api:internal` in stdlib/core | Internal implementation in critical areas |
| `priority:low` | `scope:app` + `api:internal` OR `scope:test` | Internal app code, test utilities |

**Priority matrix:**

|           | stdlib | core | lib | app | compiler |
|-----------|--------|------|-----|-----|----------|
| **public**   | critical | high | high | medium | medium |
| **internal** | medium | medium | low | low | low |

---

### 8. Severity Tags (for Warnings)

**Category:** `severity`

Used in compiler warnings to indicate importance.

| Tag | Description | Build Behavior |
|-----|-------------|----------------|
| `severity:error` | Critical missing documentation | `--warn-docs-level=error` exits with error |
| `severity:warning` | Important missing documentation | Shows warning, continues build |
| `severity:info` | Informational, nice-to-have | Shows info message |
| `severity:ignore` | Suppressed warning | No message shown |

---

## Tag Storage and Format

### In DocItem Struct

Add a `tags` field to `DocItem`:

```simple
struct DocItem:
    # ... existing fields ...
    tags: [text]  # Array of tag strings

impl DocItem:
    fn add_tag(tag: text):
        """Add a tag if not already present."""
        if not self.tags.contains(tag):
            self.tags.push(tag)

    fn has_tag(tag: text) -> bool:
        """Check if item has a specific tag."""
        self.tags.contains(tag)

    fn tags_by_category(category: text) -> [text]:
        """Get all tags in a category (e.g., 'coverage')."""
        val prefix = category + ":"
        var result: [text] = []
        for tag in self.tags:
            if tag.starts_with(prefix):
                result.push(tag)
        result

    fn remove_tag(tag: text):
        """Remove a tag if present."""
        # Implementation: filter out tag from array
        pass
```

### JSON Export Format

```json
{
  "name": "square",
  "kind": "function",
  "file": "src/std/math.spl",
  "line": 42,
  "tags": [
    "kind:function",
    "scope:stdlib",
    "api:public",
    "doc:complete",
    "doc:has_inline",
    "doc:has_sdoctest",
    "coverage:excellent",
    "priority:critical"
  ],
  "coverage_percent": 100.0
}
```

### CSV Export Format

```csv
name,kind,file,line,tags,coverage_percent
square,function,src/std/math.spl,42,"kind:function,scope:stdlib,api:public,doc:complete",100.0
helper,function,src/std/math.spl,98,"kind:function,scope:stdlib,api:internal,doc:missing_inline_comment",0.0
```

---

## Tag Generation Algorithm

### Step 1: Initialize Tags Array

```simple
fn generate_tags_for_item(item: DocItem) -> [text]:
    var tags: [text] = []

    # Add all tag categories
    tags.push(generate_kind_tag(item))
    tags.push(generate_scope_tag(item.file))
    tags.push(generate_api_tag(item))
    tags = tags + generate_doc_status_tags(item)
    tags.push(generate_coverage_tag(item))
    tags.push(generate_priority_tag(item))

    tags
```

### Step 2: Kind Tag

```simple
fn generate_kind_tag(item: DocItem) -> text:
    val kind_str = item.kind_str()  # "function", "struct", etc.
    "kind:" + kind_str
```

### Step 3: Scope Tag

```simple
fn generate_scope_tag(file_path: text) -> text:
    # See "Scope Tags" section above
    if file_path.starts_with("src/std/"):
        return "scope:stdlib"
    # ... etc.
```

### Step 4: API Tag

```simple
fn generate_api_tag(item: DocItem) -> text:
    if item.is_exported:
        "api:public"
    else:
        "api:internal"
```

### Step 5: Documentation Status Tags

```simple
fn generate_doc_status_tags(item: DocItem) -> [text]:
    var tags: [text] = []

    # Check what documentation exists
    if item.has_inline_comment:
        tags.push("doc:has_inline")
    else:
        tags.push("doc:missing_inline_comment")

    if item.has_docstring:
        tags.push("doc:has_docstring")

    if item.has_sdoctest:
        tags.push("doc:has_sdoctest")
    elif item.needs_sdoctest():
        tags.push("doc:missing_sdoctest")

    # Aggregate status
    val fully_documented = item.has_inline_comment and (not item.needs_sdoctest() or item.has_sdoctest)
    if fully_documented:
        tags.push("doc:complete")
    elif item.has_inline_comment or item.has_docstring or item.has_sdoctest:
        tags.push("doc:incomplete")
    else:
        tags.push("doc:missing_all")

    tags
```

### Step 6: Coverage Tag

```simple
fn generate_coverage_tag(item: DocItem) -> text:
    # For individual items, coverage is binary (0% or 100%)
    # For files/reports, calculate percentage

    val is_documented = item.is_documented()
    if is_documented:
        "coverage:excellent"  # 100% for individual items
    else:
        "coverage:none"
```

### Step 7: Priority Tag

```simple
fn generate_priority_tag(item: DocItem) -> text:
    val scope_tag = generate_scope_tag(item.file)
    val api_tag = generate_api_tag(item)

    # Critical: public stdlib
    if scope_tag == "scope:stdlib" and api_tag == "api:public":
        return "priority:critical"

    # High: public core/lib
    if (scope_tag == "scope:core" or scope_tag == "scope:lib") and api_tag == "api:public":
        return "priority:high"

    # Medium: internal stdlib/core or public app
    if scope_tag == "scope:stdlib" or scope_tag == "scope:core":
        return "priority:medium"
    if scope_tag == "scope:app" and api_tag == "api:public":
        return "priority:medium"

    # Low: everything else
    "priority:low"
```

---

## CLI Integration

### Filtering by Tags

```bash
# Show all items with specific tag
simple doc-coverage --tag=scope:stdlib
simple doc-coverage --tag=doc:missing_sdoctest

# Multiple tag filters (AND logic)
simple doc-coverage --tag=scope:stdlib --tag=api:public

# Show only items with specific coverage level
simple doc-coverage --tag=coverage:poor
simple doc-coverage --tag=coverage:insufficient

# Filter by priority
simple doc-coverage --tag=priority:critical --missing
```

### Tag Statistics

```bash
# Count items by tag
simple stats --doc-coverage-only --group-by=scope
simple stats --doc-coverage-only --group-by=priority

# Output:
# Scope Breakdown:
#   stdlib:   120 items (95% documented)
#   core:      89 items (87% documented)
#   lib:       45 items (78% documented)
#   app:      234 items (52% documented)
```

### JSON Export with Tags

```bash
simple stats --format=json --doc-coverage-only > doc_coverage.json

# Output includes full tag arrays for each item
```

---

## Usage Examples

### Example 1: Finding Critical Missing Docs

**Command:**
```bash
simple doc-coverage --tag=priority:critical --tag=doc:missing_sdoctest
```

**Output:**
```
Missing SDoctest in Critical APIs (src/std/)
============================================

src/std/text.spl:42 - fn split(delimiter: text) -> [text]
  Tags: kind:function, scope:stdlib, api:public, doc:missing_sdoctest, priority:critical

src/std/array.spl:89 - fn filter(predicate: fn(T) -> bool) -> [T]
  Tags: kind:function, scope:stdlib, api:public, doc:missing_sdoctest, priority:critical

Total: 2 items need documentation
```

### Example 2: Scope-Level Coverage Report

**Command:**
```bash
simple stats --doc-coverage-only --group-by=scope
```

**Output:**
```
Documentation Coverage by Scope
================================

scope:stdlib (120 items)
  Coverage: 95% (114/120 documented)
  Missing: 6 items
  Tags: coverage:excellent

scope:core (89 items)
  Coverage: 87% (77/89 documented)
  Missing: 12 items
  Tags: coverage:good

scope:lib (45 items)
  Coverage: 78% (35/45 documented)
  Missing: 10 items
  Tags: coverage:acceptable

scope:app (234 items)
  Coverage: 52% (122/234 documented)
  Missing: 112 items
  Tags: coverage:poor
```

### Example 3: Priority-Based Filtering

**Command:**
```bash
simple build --warn-docs --warn-docs-priority=critical
```

**Output:**
```
warning: missing sdoctest for public stdlib function
  --> src/std/text.spl:42:1
   |
42 | fn split(delimiter: text) -> [text]:
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: Tags: priority:critical, doc:missing_sdoctest
   = help: Add sdoctest example in docstring

2 warnings emitted (priority:critical only)
```

### Example 4: JSON Export with Tags

**Command:**
```bash
simple stats --format=json --doc-coverage-only | jq '.items[] | select(.tags[] | contains("priority:critical"))'
```

**Output:**
```json
{
  "name": "split",
  "kind": "function",
  "file": "src/std/text.spl",
  "line": 42,
  "signature": "fn split(delimiter: text) -> [text]",
  "tags": [
    "kind:function",
    "scope:stdlib",
    "api:public",
    "doc:has_inline",
    "doc:missing_sdoctest",
    "doc:incomplete",
    "coverage:insufficient",
    "priority:critical"
  ],
  "coverage_percent": 50.0
}
```

---

## Implementation Checklist

### Phase 1: Core Tag Generation (2 hours)
- [ ] Add `tags: [text]` field to `DocItem` struct
- [ ] Implement `generate_kind_tag()`
- [ ] Implement `generate_scope_tag()`
- [ ] Implement `generate_api_tag()`
- [ ] Implement `generate_doc_status_tags()`
- [ ] Implement `generate_coverage_tag()`
- [ ] Implement `generate_priority_tag()`
- [ ] Create `src/app/doc_coverage/tagging/tag_generator.spl`
- [ ] Add tests for tag generation

### Phase 2: Tag Utilities (1 hour)
- [ ] Implement `DocItem.add_tag()`
- [ ] Implement `DocItem.has_tag()`
- [ ] Implement `DocItem.tags_by_category()`
- [ ] Implement `DocItem.remove_tag()`
- [ ] Create `src/app/doc_coverage/tagging/tag_validator.spl`
- [ ] Add tag validation (format checking)
- [ ] Add tests for tag utilities

### Phase 3: Integration (1 hour)
- [ ] Call tag generation in file scanner
- [ ] Add tags to JSON export format
- [ ] Add tags to CSV export format
- [ ] Update `src/app/stats/json_formatter.spl`
- [ ] Add CLI flags: `--tag=<filter>`
- [ ] Add `--group-by=<category>` flag
- [ ] Add tests for filtering

### Phase 4: Reporting (1 hour)
- [ ] Add tag statistics to terminal output
- [ ] Show tag breakdown in reports
- [ ] Add tag filtering to `simple doc-coverage` command
- [ ] Update markdown report generator with tags
- [ ] Add tests for tag reporting

### Phase 5: Documentation (30 minutes)
- [ ] Update `CLAUDE.md` with tag examples
- [ ] Create `doc/guide/doc_coverage_tags.md` (user guide)
- [ ] Add examples to `README.md`

---

## Tag Extension Guidelines

### Adding a New Tag Category

1. **Define the category name** (lowercase, singular)
2. **List all possible values** (lowercase, underscores)
3. **Document detection logic** (how to determine the tag value)
4. **Update tag generator** (add new `generate_<category>_tag()` function)
5. **Add tests** for new tag generation
6. **Update documentation** (this design doc + user guide)

### Example: Adding `test` Category

```simple
# New category: test status
# Tags: test:passing, test:failing, test:skipped, test:none

fn generate_test_tag(item: DocItem) -> text:
    # Check if item has tests
    val has_tests = item.has_sdoctest or _has_spec_file(item)
    if not has_tests:
        return "test:none"

    # Run tests and check status (if available)
    val test_result = _get_test_result(item)
    match test_result:
        "pass": "test:passing"
        "fail": "test:failing"
        "skip": "test:skipped"
        _: "test:none"
```

---

## Future Enhancements

### Planned Tag Categories

1. **Complexity Tags** - `complexity:high`, `complexity:medium`, `complexity:low`
   - Based on cyclomatic complexity or function length
2. **Deprecation Tags** - `deprecated:yes`, `deprecated:no`
   - Detect `@deprecated` annotations
3. **Stability Tags** - `stability:stable`, `stability:unstable`, `stability:experimental`
   - Parse `@stability` annotations
4. **Author Tags** - `author:<username>`
   - Extract from git blame or `@author` annotations
5. **Changed Tags** - `changed:recent`, `changed:stale`
   - Git history analysis (modified in last 30 days)

### Tag Relationships

Future: Define tag dependencies and conflicts

```yaml
tag_rules:
  conflicts:
    - [doc:complete, doc:missing_all]
    - [coverage:excellent, coverage:none]
  implies:
    - doc:complete -> doc:has_inline
    - api:public + kind:function -> needs_sdoctest
```

---

## Success Metrics

1. **Tag Consistency:** 100% of items have all required tags (kind, scope, api, coverage, priority)
2. **Tag Accuracy:** Manual review of 50 items shows 95%+ correct tag assignment
3. **CLI Usability:** `--tag=<filter>` reduces output to relevant items
4. **Performance:** Tag generation adds <5% overhead to coverage analysis
5. **Documentation:** User guide with 10+ tag filtering examples

---

## Appendix: Complete Tag Reference

### All Tag Categories

| Category | Values | Auto-Generated | Count |
|----------|--------|----------------|-------|
| `coverage` | excellent, good, acceptable, poor, insufficient, none | ✅ | 6 |
| `doc` | complete, incomplete, missing_inline_comment, missing_sdoctest, missing_group_comment, missing_all, has_inline, has_docstring, has_sdoctest | ✅ | 9 |
| `scope` | stdlib, core, lib, app, compiler, test, unknown | ✅ | 7 |
| `api` | public, internal, exported, private | ✅ | 4 |
| `group` | documented, undocumented, partial | ✅ | 3 |
| `kind` | function, struct, class, enum, variant, constant, variable, module, impl | ✅ | 9 |
| `priority` | critical, high, medium, low | ✅ | 4 |
| `severity` | error, warning, info, ignore | ✅ | 4 |

**Total:** 8 categories, 46 unique tag values

### Tag Naming Patterns

```
coverage:{level}        # Coverage percentage bracket
doc:{status}           # Documentation presence/absence
scope:{location}       # Codebase location
api:{visibility}       # Public vs internal
group:{state}          # Variable group documentation
kind:{type}            # Item type (function, struct, etc.)
priority:{level}       # Documentation priority
severity:{level}       # Warning severity
```

---

## See Also

- `doc/guide/doc_coverage_user_guide.md` - User-facing guide with examples
- `src/app/doc_coverage/types/doc_item.spl` - DocItem struct definition
- `src/app/doc_coverage/tagging/tag_generator.spl` - Tag generation implementation (to be created)
- `DOC_COVERAGE_ENHANCEMENT_PLAN.md` - Overall enhancement plan
