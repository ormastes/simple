# Documentation Coverage: Compiler Warnings & Thresholds Design

**Date:** 2026-02-14
**Status:** Design Phase
**Features:** Compiler warning integration, Coverage thresholds, Enhanced statistics

---

## 1. Overview

Enhance the doc_coverage system with two major features:

1. **Compiler Warnings**: Emit warnings during `simple build` for missing documentation
2. **Coverage Thresholds**: Configurable sdoctest coverage requirements with automatic tagging

**Key Insight:** Sdoctest = **function coverage** (code examples in docs demonstrating function usage)

---

## 2. Public API Detection

### Current Pattern (Discovered)
- **`__init__.spl`** or **`mod.spl`** in each directory define public API
- Pattern: `from submodule import {items}` → `export items`
- Only exported items are considered "public"

### Enhanced Detection Algorithm
```simple
fn is_public_function(func_name: text, file_path: text) -> bool:
    # 1. Find nearest __init__.spl or mod.spl parent
    val module_file = find_module_init(file_path)
    if module_file == nil:
        return false  # No module export file = internal

    # 2. Parse export statements
    val exports = parse_exports(module_file)

    # 3. Check if function is exported
    return exports.contains(func_name)
```

**Examples:**
- `src/std/text.spl` function `str_len()` → Check `src/std/__init__.spl` exports
- If exported → public, requires sdoctest
- If not exported → internal, lower threshold

---

## 3. Feature 1: Compiler Warning Integration

### 3.1 Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  simple build [--warn-docs] [--warn-docs-level=error]       │
└───────────────┬─────────────────────────────────────────────┘
                │
                ▼
┌───────────────────────────────────────────────────────────────┐
│  CLI: src/app/cli/main.spl                                    │
│  - Parse --warn-docs flags                                    │
│  - Pass to build system                                       │
└───────────────┬───────────────────────────────────────────────┘
                │
                ▼
┌───────────────────────────────────────────────────────────────┐
│  Build System: src/compiler/driver.spl                        │
│  - After parsing, before codegen                              │
│  - Call doc_coverage analysis                                 │
│  - Emit warnings via diagnostic system                        │
└───────────────┬───────────────────────────────────────────────┘
                │
                ▼
┌───────────────────────────────────────────────────────────────┐
│  Doc Coverage: src/app/doc_coverage/analysis/mod.spl          │
│  - New module: compiler_warnings.spl                          │
│  - Scan parsed AST for functions                              │
│  - Check exports in __init__.spl/mod.spl                      │
│  - Generate warning objects                                   │
└───────────────┬───────────────────────────────────────────────┘
                │
                ▼
┌───────────────────────────────────────────────────────────────┐
│  Diagnostics: src/std/common/diagnostic.spl                   │
│  - Emit warnings with file:line info                          │
│  - Severity: INFO/WARN/ERROR                                  │
│  - Format: "Missing sdoctest for public function `func_name`" │
└───────────────────────────────────────────────────────────────┘
```

### 3.2 CLI Flags

| Flag | Default | Description |
|------|---------|-------------|
| `--warn-docs` | off | Enable doc coverage warnings |
| `--no-warn-docs` | - | Explicitly disable (override config) |
| `--warn-docs-level=LEVEL` | warn | Severity: `info`, `warn`, `error` |
| `--warn-docs-public-only` | on | Only warn for public API |
| `--warn-docs-fail-on-error` | off | Exit with error if any warnings |

### 3.3 Warning Categories

| Category | Severity | Condition | Message |
|----------|----------|-----------|---------|
| **missing_sdoctest** | WARN | Public function lacks sdoctest | `Missing sdoctest for public function 'func_name'` |
| **missing_inline_comment** | INFO | Function lacks inline comment | `Missing inline comment for function 'func_name'` |
| **missing_group_comment** | INFO | Variable group lacks comment | `Missing group comment for N related variables` |
| **insufficient_coverage** | ERROR | Module below threshold | `Module coverage 45% < threshold 80%` |

### 3.4 Warning Format

```
warning[missing_sdoctest]: Missing sdoctest for public function `str_len`
  --> src/std/text.spl:42:1
   |
42 | fn str_len(s: text) -> i64:
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^ function lacks documentation example
   |
   = help: Add an sdoctest block in README.md or doc/guide/*.md
   = help: Example:
           ```simple
           val len = str_len("hello")
           print len  # 5
           ```
```

### 3.5 Integration Points

**New File:** `src/app/doc_coverage/analysis/compiler_warnings.spl`

```simple
# Compiler warning integration for doc coverage

use app.doc_coverage.types.{DocItem, DocKind}
use std.common.diagnostic.{Diagnostic, Severity, Span}

fn emit_doc_warnings(items: [DocItem], config: WarnConfig) -> [Diagnostic]:
    var warnings = []

    for item in items:
        # Check if public (via exports)
        if not item.is_public and config.public_only:
            continue

        # Missing sdoctest (functions only)
        if item.kind == DocKind.Function and not item.has_sdoctest:
            val warn = make_warning(
                "missing_sdoctest",
                item.file,
                item.line,
                "Missing sdoctest for public function '{item.name}'",
                config.severity
            )
            warnings = warnings + [warn]

        # Missing inline comment
        if not item.has_inline_comment and config.warn_inline:
            val warn = make_warning(
                "missing_inline_comment",
                item.file,
                item.line,
                "Missing inline comment for {kind_name(item.kind)} '{item.name}'",
                Severity.Info
            )
            warnings = warnings + [warn]

    return warnings
```

**Modify:** `src/compiler/driver.spl` (or wherever build happens)

```simple
fn build_with_warnings(files: [text], config: BuildConfig):
    # ... existing parsing ...

    if config.warn_docs:
        val doc_items = scan_all_for_docs(files)
        val warnings = emit_doc_warnings(doc_items, config.warn_docs_config)

        for warn in warnings:
            emit_diagnostic(warn)

        if config.fail_on_error and has_errors(warnings):
            exit(1)

    # ... continue to codegen ...
```

---

## 4. Feature 2: Coverage Thresholds

### 4.1 Threshold Configuration

**Config File:** `doc_coverage.sdn` (project root)

```sdn
doc_coverage {
    # Global threshold (default if no specific override)
    default_threshold 70

    # Per-scope thresholds
    thresholds {
        "src/std/" 90     # Stdlib: high standard
        "src/compiler_core/" 75    # Core: medium-high
        "src/lib/" 80     # Libraries: high
        "src/app/" 50     # Applications: lower
        "src/compiler/" 60
    }

    # Enforcement
    enforce_thresholds true
    fail_on_below_threshold false  # Just warn, don't fail build

    # What counts as "covered"
    coverage_rules {
        # Require sdoctest for public functions
        public_functions_require_sdoctest true

        # Internal functions don't need sdoctest
        internal_functions_require_sdoctest false

        # Structs/classes need inline comments
        types_require_inline_comment true
    }

    # Exclusions (files/patterns to ignore)
    exclude [
        "src/app/cli/main.spl"  # CLI glue code
        "test/**"               # Test files
        "**/deprecated/**"      # Deprecated code
    ]
}
```

### 4.2 Threshold Calculation

```simple
struct ThresholdResult:
    scope: text           # "src/std/", "src/compiler_core/", etc.
    threshold: i64        # Required percentage (0-100)
    actual: i64           # Actual coverage percentage
    passed: bool          # actual >= threshold
    total_functions: i64
    covered_functions: i64
    missing_functions: [text]  # Names of functions lacking sdoctests

fn calculate_coverage(files: [text], config: ThresholdConfig) -> [ThresholdResult]:
    var results = []

    # Group files by scope (src/std/, src/compiler_core/, etc.)
    val groups = group_by_scope(files)

    for scope in groups.keys():
        val scope_files = groups[scope]
        val threshold = config.get_threshold(scope)

        # Scan for public functions
        val items = scan_files_for_docs(scope_files)
        val public_funcs = items.filter(\i: i.kind == DocKind.Function and i.is_public)

        # Calculate coverage
        val total = public_funcs.len()
        val covered = public_funcs.filter(\f: f.has_sdoctest).len()
        val actual = if total == 0: 100 else: (covered * 100) / total

        val result = ThresholdResult(
            scope: scope,
            threshold: threshold,
            actual: actual,
            passed: actual >= threshold,
            total_functions: total,
            covered_functions: covered,
            missing_functions: public_funcs
                .filter(\f: not f.has_sdoctest)
                .map(\f: f.name)
        )

        results = results + [result]

    return results
```

### 4.3 Threshold Tags

Auto-generated tags for functions/modules based on coverage:

| Tag | Condition | Meaning |
|-----|-----------|---------|
| `coverage:excellent` | ≥95% | Excellent documentation |
| `coverage:good` | 80-94% | Good coverage |
| `coverage:acceptable` | 60-79% | Acceptable |
| `coverage:poor` | 40-59% | Below standard |
| `coverage:insufficient` | <40% | Critical gaps |
| `sdoctest:missing` | Function lacks example | Needs sdoctest |
| `sdoctest:present` | Has example | Well documented |

### 4.4 Threshold Report

**Output Format (Markdown):**

```markdown
# Documentation Coverage Threshold Report
Generated: 2026-02-14 10:30:00

## Summary
- **Total Scopes:** 5
- **Passed Thresholds:** 3 (60%)
- **Failed Thresholds:** 2 (40%)

## Threshold Results

### ✅ src/std/ (PASSED)
- **Threshold:** 90%
- **Actual:** 92% (147/160 functions)
- **Status:** PASS
- **Missing:** 13 functions

### ✅ src/compiler_core/ (PASSED)
- **Threshold:** 75%
- **Actual:** 78% (89/114 functions)
- **Status:** PASS
- **Missing:** 25 functions

### ❌ src/lib/ (FAILED)
- **Threshold:** 80%
- **Actual:** 68% (34/50 functions)
- **Status:** FAIL (12% below threshold)
- **Missing:** 16 functions
  - `database.query_builder.build_select`
  - `database.query_builder.build_where`
  - ... (14 more)

### ✅ src/app/ (PASSED)
- **Threshold:** 50%
- **Actual:** 55% (22/40 functions)
- **Status:** PASS
- **Missing:** 18 functions

### ❌ src/compiler/ (FAILED)
- **Threshold:** 60%
- **Actual:** 42% (50/119 functions)
- **Status:** FAIL (18% below threshold)
- **Missing:** 69 functions

## Recommendations
1. Focus on `src/lib/` - only 12% below threshold (16 functions)
2. `src/compiler/` needs major effort (69 missing sdoctests)
3. Add sdoctests to README.md or doc/guide/compiler.md
```

### 4.5 CLI Integration

```bash
# Check thresholds (no warnings during build)
simple doc-coverage --thresholds
simple doc-coverage --thresholds --config=custom_thresholds.sdn

# Generate threshold report
simple doc-coverage --thresholds --report=threshold_report.md

# Fail on below-threshold (CI mode)
simple doc-coverage --thresholds --fail-on-below

# Show which functions need sdoctests
simple doc-coverage --thresholds --list-missing

# Tag functions based on coverage
simple doc-coverage --thresholds --tag-file=coverage_tags.txt
```

---

## 5. Enhanced Statistics

### 5.1 New Statistics to Track

**Per Module:**
- Public function count (from exports)
- Internal function count (not exported)
- Sdoctest coverage % (public only)
- Inline comment coverage % (all)
- Group comment coverage % (variable groups)

**Per Function:**
- Is exported (public API)
- Has sdoctest
- Has inline comment
- Has docstring
- Parent module path
- Suggested tag

**Trends (if run multiple times):**
- Coverage change over time
- Functions added/removed
- Documentation debt (functions added without sdoctests)

### 5.2 Statistics Output Format

**JSON Export** (`--format=json`):

```json
{
  "timestamp": "2026-02-14T10:30:00Z",
  "summary": {
    "total_files": 604,
    "total_functions": 2847,
    "public_functions": 1203,
    "internal_functions": 1644,
    "sdoctest_coverage_percent": 67,
    "inline_comment_coverage_percent": 82
  },
  "by_scope": {
    "src/std/": {
      "threshold": 90,
      "actual": 92,
      "passed": true,
      "total_functions": 160,
      "public_functions": 160,
      "covered_functions": 147,
      "missing_functions": ["str_reverse", "str_trim", ...]
    },
    "src/compiler_core/": { ... }
  },
  "functions": [
    {
      "name": "str_len",
      "file": "src/std/text.spl",
      "line": 42,
      "is_public": true,
      "has_sdoctest": true,
      "has_inline_comment": true,
      "has_docstring": true,
      "tags": ["coverage:excellent", "sdoctest:present"]
    },
    ...
  ]
}
```

**CSV Export** (`--format=csv`):

```csv
name,file,line,is_public,has_sdoctest,has_inline,has_docstring,tags
str_len,src/std/text.spl,42,true,true,true,true,"coverage:excellent;sdoctest:present"
str_reverse,src/std/text.spl,67,true,false,true,false,"coverage:poor;sdoctest:missing"
...
```

---

## 6. Implementation Phases

### Phase 1: Public API Detection (Week 1)
**Files to Create:**
- `src/app/doc_coverage/analysis/export_parser.spl` (parse `__init__.spl`/`mod.spl`)

**Tasks:**
1. Implement `find_module_init(file_path)` → finds nearest `__init__.spl`/`mod.spl`
2. Implement `parse_exports(module_file)` → extracts exported names
3. Update `DocItem` struct with `is_exported: bool` field
4. Write tests for export detection

### Phase 2: Compiler Warning Integration (Week 1-2)
**Files to Create:**
- `src/app/doc_coverage/analysis/compiler_warnings.spl`

**Files to Modify:**
- `src/app/cli/main.spl` (add `--warn-docs*` flags)
- `src/compiler/driver.spl` or build entry point (call doc analysis)

**Tasks:**
1. Implement `emit_doc_warnings(items, config)` → generates diagnostics
2. Integrate with diagnostic system (`std.common.diagnostic`)
3. Add CLI flags and config parsing
4. Write tests for warning generation
5. Test integration with build system

### Phase 3: Threshold System (Week 2)
**Files to Create:**
- `src/app/doc_coverage/analysis/thresholds.spl`
- `doc_coverage.sdn` (default config template)

**Tasks:**
1. Implement SDN config parser for thresholds
2. Implement `calculate_coverage(files, config)` → threshold results
3. Add threshold checking to doc-coverage command
4. Generate threshold report (markdown/json/csv)
5. Write tests for threshold calculation

### Phase 4: Enhanced Statistics (Week 3)
**Files to Modify:**
- `src/app/doc_coverage/types/coverage_result.spl` (add new stats)
- `src/app/doc_coverage/analysis/mod.spl` (aggregate stats)

**Tasks:**
1. Add JSON/CSV export formats
2. Track public vs internal functions separately
3. Add trend tracking (optional, future feature)
4. Generate comprehensive reports

### Phase 5: Testing & Documentation (Week 3)
**Files to Create:**
- `test/unit/app/doc_coverage/export_parser_spec.spl`
- `test/unit/app/doc_coverage/compiler_warnings_spec.spl`
- `test/unit/app/doc_coverage/thresholds_spec.spl`
- `doc/guide/doc_coverage_thresholds.md`

**Tasks:**
1. Write comprehensive test suite
2. Test with real project (self-test on Simple compiler)
3. Write user guide
4. Update CLAUDE.md with new commands

---

## 7. Tag Naming Scheme

### 7.1 Coverage Tags (Auto-Generated)

| Category | Tags | Description |
|----------|------|-------------|
| **coverage** | excellent, good, acceptable, poor, insufficient | Module/file coverage level |
| **sdoctest** | present, missing, incomplete | Function has/lacks examples |
| **inline_comment** | present, missing | Has/lacks inline comment |
| **group_comment** | present, missing | Variable groups |
| **public_api** | exported, internal | Visibility level |

### 7.2 Tag Format

- **Lowercase only:** `coverage:excellent` NOT `Coverage:Excellent`
- **Underscores for multi-word:** `inline_comment:missing`
- **Colon separator:** `category:value`
- **No spaces:** Use `_` instead

### 7.3 Composite Tags (Optional)

For nuanced status:
- `sdoctest:present_but_insufficient` - Has example but too trivial
- `coverage:good_but_declining` - Was excellent, now good (trend)
- `public_api:exported_but_deprecated` - Public but scheduled for removal

---

## 8. Example Workflow

### Developer Workflow

```bash
# Daily: Check docs while developing
simple build --warn-docs

# Output:
# warning[missing_sdoctest]: Missing sdoctest for public function `new_feature`
#   --> src/std/feature.spl:42:1
#
# Build succeeded with 1 warning

# Before commit: Check thresholds
simple doc-coverage --thresholds

# Output:
# ✅ src/std/ (92% >= 90%)
# ❌ src/lib/ (68% < 80%)
#
# Threshold check: 4/5 passed (80%)

# Add sdoctests to README.md, then re-check
simple doc-coverage --thresholds --list-missing
```

### CI/CD Workflow

```bash
# .github/workflows/docs.yml
- name: Check documentation coverage
  run: |
    simple doc-coverage --thresholds --fail-on-below
    simple build --warn-docs --warn-docs-level=error --warn-docs-fail-on-error
```

---

## 9. Open Questions

1. **Threshold granularity:** Should we support per-file thresholds or just per-directory?
2. **Exemptions:** How to mark certain functions as exempt from sdoctest requirement? (e.g., private helpers, deprecated)
3. **Integration timing:** Run doc checks during parse or after full AST available?
4. **Performance:** Cache export parsing results? Doc coverage can be slow on large codebases
5. **Backwards compatibility:** Should warnings be opt-in or opt-out by default?

---

## 10. Success Metrics

- **Phase 1:** Export detection works for all 604 files
- **Phase 2:** Warnings emit correctly, build still succeeds
- **Phase 3:** Threshold system accurately reports coverage
- **Phase 4:** JSON/CSV export used in CI pipelines
- **Phase 5:** 100% test coverage for new modules

**End Goal:** 90%+ public function sdoctest coverage across `src/std/` and `src/compiler_core/`
