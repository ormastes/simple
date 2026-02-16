# Documentation Coverage Enhancement Design
**Date:** 2026-02-14
**Status:** Design Phase
**Implementation:** Multi-Agent

## Overview

Extend the Simple compiler's statistics and documentation coverage system with:

1. **SDoctest Coverage Comparison** - Compare public function count to sdoctest examples
2. **Insufficient Documentation Tagging** - Auto-tag functions needing better docs
3. **Tag Naming Standards** - Hierarchical tag taxonomy
4. **Inline Comment Tracking** - Count missing inline comments
5. **Compiler Warning Integration** - Emit warnings during build
6. **Group Comment Detection** - Tag related var/func groups

## Current Infrastructure

**Already Implemented:**
- ✅ SDoctest coverage analysis (`src/app/doc_coverage/analysis/sdoctest_coverage.spl`)
- ✅ Inline comment coverage (`src/app/doc_coverage/analysis/inline_comment_coverage.spl`)
- ✅ Group comment detection (`src/app/doc_coverage/analysis/group_comment_detection.spl`)
- ✅ Compiler warnings (`src/app/doc_coverage/compiler_warnings.spl`)
- ✅ Statistics system (`src/app/stats/dynamic.spl`)
- ✅ DocItem type system (`src/app/doc_coverage/types/doc_item.spl`)

**What's Missing:**
- ❌ Integration of all coverage features into unified report
- ❌ Enhanced tag classification system
- ❌ Threshold-based warning levels
- ❌ Compiler build integration (`--warn-docs`)
- ❌ Multi-file aggregation and trends
- ❌ JSON export for CI/CD

---

## Feature 1: SDoctest Coverage Comparison

### Design

**Current State:**
- `compute_doc_coverage()` in `stats/dynamic.spl` already computes:
  - `total_public` - all public functions
  - `documented` - functions with any docs
  - `with_sdoctest` - functions appearing in sdoctest blocks

**Enhancement:**
```simple
struct SDocCoverageStats:
    total_public_functions: i64
    functions_with_docs: i64
    functions_with_sdoctest: i64
    functions_without_sdoctest: i64
    coverage_percent: i64
    sdoctest_percent: i64
    missing_sdoctest: [text]  # Function names needing examples
```

**Implementation:**
- Extend `stats/dynamic.spl` to return detailed breakdown
- Add `--doc-coverage` flag to show detailed report
- Export missing function names for tagging

**Example Output:**
```
Documentation Coverage:
  Public Functions:     342
  With Documentation:   298 (87%)
  With SDoctest:        156 (46%)
  Missing SDoctest:     186 (54%)

Top functions needing examples:
  - src/std/text.spl:split_lines
  - src/std/array.spl:flatten
  - src/core/parser.spl:parse_expression
```

---

## Feature 2: Tag Classification System

### Tag Taxonomy

**Hierarchical Tag Structure:**

```
doc_status:<level>
├─ doc_status:complete      # Has inline + docstring + sdoctest
├─ doc_status:documented    # Has inline + docstring, no sdoctest
├─ doc_status:partial       # Has only inline OR docstring
└─ doc_status:missing       # No documentation

sdoctest:<quality>
├─ sdoctest:comprehensive   # 3+ examples, covers edge cases
├─ sdoctest:basic          # 1-2 examples, basic usage
├─ sdoctest:missing        # No sdoctest examples
└─ sdoctest:insufficient   # Has examples but incomplete

visibility:<scope>
├─ visibility:public       # Exported, in public API
├─ visibility:internal     # Module-level, not exported
└─ visibility:private      # Implementation detail

item_kind:<type>
├─ item_kind:function
├─ item_kind:struct
├─ item_kind:class
├─ item_kind:enum
└─ item_kind:constant

priority:<urgency>
├─ priority:critical       # Public API, no docs
├─ priority:high           # Public API, partial docs
├─ priority:medium         # Public API, needs sdoctest
└─ priority:low            # Internal, docs optional

module:<category>
├─ module:stdlib          # src/std/*
├─ module:core            # src/core/*
├─ module:compiler        # src/compiler/*
├─ module:app             # src/app/*
└─ module:lib             # src/lib/*
```

### Tag Assignment Logic

```simple
fn classify_doc_item(item: DocItem) -> [text]:
    var tags: [text] = []

    # Doc status
    if item.has_inline_comment and item.has_docstring and item.has_sdoctest:
        tags.push("doc_status:complete")
    elif item.has_inline_comment and item.has_docstring:
        tags.push("doc_status:documented")
    elif item.has_inline_comment or item.has_docstring:
        tags.push("doc_status:partial")
    else:
        tags.push("doc_status:missing")

    # SDoctest quality
    val sdoc_count = count_sdoctest_examples(item.name)
    if sdoc_count >= 3:
        tags.push("sdoctest:comprehensive")
    elif sdoc_count >= 1:
        tags.push("sdoctest:basic")
    else:
        tags.push("sdoctest:missing")

    # Visibility
    if item.is_exported:
        tags.push("visibility:public")
    elif item.visibility == "pub":
        tags.push("visibility:internal")
    else:
        tags.push("visibility:private")

    # Item kind
    val kind_tag = "item_kind:{item.kind_str()}"
    tags.push(kind_tag)

    # Priority (based on visibility + doc status)
    if item.is_exported:
        if not item.has_inline_comment and not item.has_docstring:
            tags.push("priority:critical")
        elif not item.has_sdoctest:
            tags.push("priority:medium")
        else:
            tags.push("priority:low")

    # Module category
    val module_tag = infer_module_tag(item.file)
    tags.push(module_tag)

    tags
```

---

## Feature 3: Inline Comment Tracking

### Design

**Already Implemented:**
- `InlineCommentResult` struct in `inline_comment_coverage.spl`
- Detection of missing inline comments
- Warning level classification (error/warn/info/none)

**Enhancement:**
```simple
struct InlineCommentStats:
    total_items: i64
    with_inline_comment: i64
    with_docstring: i64
    with_both: i64
    with_neither: i64
    by_kind: [(text, i64)]  # (kind, count) pairs
    error_items: [text]     # Item names with errors
    warn_items: [text]      # Item names with warnings
```

**Integration:**
- Add `--inline-coverage` flag to stats command
- Include in JSON export
- Emit compiler warnings when enabled

---

## Feature 4: Group Comment Detection

### Design

**Already Implemented:**
- `VariableGroup` struct in `group_comment_detection.spl`
- Detection of consecutive var/val declarations
- Smart comment suggestions (prefix/suffix/pattern detection)

**Enhancement Tags:**
```
group_comment:present
group_comment:missing
var_group:<pattern>
├─ var_group:config
├─ var_group:state
├─ var_group:constants
├─ var_group:cache
├─ var_group:buffer
├─ var_group:counter
└─ var_group:flag
```

**Integration:**
- Add to statistics summary
- Generate warnings for missing group comments
- Suggest improvements in build output

---

## Feature 5: Compiler Warning Integration

### Build Integration

**CLI Flags:**
```bash
simple build --warn-docs              # Emit all doc warnings
simple build --warn-docs=error        # Treat as errors
simple build --warn-docs=critical     # Only critical items
simple build --doc-threshold=80       # Fail if coverage < 80%
```

**Warning Levels:**
```simple
enum DocWarningLevel:
    Error      # Missing docs on public API
    Warn       # Partial docs on public API
    Info       # Missing sdoctest on documented functions
    Note       # Group comment suggestions
```

**Output Format:**
```
warning[doc-missing]: missing documentation for function `parse_expr`
  --> src/core/parser.spl:145
  |
145| fn parse_expr():
  |    ^^^^^^^^^^
  |
  = help: add inline comment and docstring
  = help: add sdoctest example in doc/guide/parsing.md

info[sdoctest-missing]: public function lacks usage example
  --> src/std/text.spl:89
  |
  = note: function is documented but has no sdoctest
  = help: add example to README.md or doc/guide/stdlib.md
```

**Implementation:**
- Hook into `src/app/build/orchestrator.spl`
- Call `check_file_documentation()` for each compiled file
- Aggregate warnings and emit at end
- Exit with error code if threshold violated

---

## Feature 6: Enhanced Statistics JSON Export

### JSON Schema

```json
{
  "files": {
    "total": 342,
    "app": 125,
    "lib": 18,
    "std": 87,
    "tests": 112
  },
  "documentation": {
    "total_public_items": 1248,
    "documented_items": 1087,
    "with_sdoctest": 542,
    "doc_percent": 87,
    "sdoctest_percent": 43,
    "by_kind": {
      "function": {"total": 987, "documented": 856, "with_sdoctest": 412},
      "struct": {"total": 143, "documented": 143, "with_sdoctest": 89},
      "class": {"total": 67, "documented": 56, "with_sdoctest": 28},
      "enum": {"total": 51, "documented": 32, "with_sdoctest": 13}
    },
    "by_module": {
      "stdlib": {"total": 456, "documented": 423, "sdoctest": 234},
      "core": {"total": 312, "documented": 287, "sdoctest": 145},
      "compiler": {"total": 234, "documented": 198, "sdoctest": 87},
      "app": {"total": 246, "documented": 179, "sdoctest": 76}
    }
  },
  "inline_comments": {
    "total_items": 1248,
    "with_inline": 1087,
    "with_docstring": 876,
    "with_both": 765,
    "with_neither": 161,
    "errors": 23,
    "warnings": 87,
    "info": 156
  },
  "group_comments": {
    "total_groups": 45,
    "with_comment": 32,
    "missing_comment": 13,
    "by_pattern": {
      "config": 12,
      "state": 8,
      "constants": 15,
      "cache": 4,
      "buffer": 3,
      "counter": 2,
      "flag": 1
    }
  },
  "warnings": {
    "critical": 23,
    "high": 87,
    "medium": 156,
    "low": 234
  }
}
```

---

## Multi-Agent Implementation Plan

### Phase 1: Foundation (Code Agent)
**Duration:** 2 hours
**Files:** 3-5 new modules

**Tasks:**
1. Create `src/app/stats/doc_coverage.spl` - unified coverage aggregation
2. Create `src/app/stats/tag_classifier.spl` - tag assignment logic
3. Extend `src/app/stats/json_formatter.spl` - enhanced JSON schema
4. Add `DocCoverageStats` struct to `types.spl`

**Output:**
- Complete data aggregation pipeline
- Tag classification system
- JSON export with all metrics

---

### Phase 2: Compiler Integration (Infra Agent)
**Duration:** 1.5 hours
**Files:** 2-3 modified modules

**Tasks:**
1. Modify `src/app/build/orchestrator.spl` - add doc checking hook
2. Modify `src/app/build/config.spl` - add `warn_docs` flags
3. Extend `src/app/doc_coverage/compiler_warnings.spl` - threshold checking

**Output:**
- `--warn-docs` flag working
- Warnings emitted during build
- Threshold enforcement

---

### Phase 3: Statistics Enhancement (Code Agent)
**Duration:** 2 hours
**Files:** 4-5 modified modules

**Tasks:**
1. Extend `src/app/stats/dynamic.spl` - integrate all coverage features
2. Add CLI flags: `--doc-coverage`, `--inline-coverage`, `--group-coverage`
3. Create detailed reports for each coverage type
4. Add comparison to previous runs (trend tracking)

**Output:**
- Comprehensive stats output
- Per-module breakdowns
- Trend analysis

---

### Phase 4: Testing (Test Agent)
**Duration:** 2 hours
**Files:** 6-8 test files

**Tasks:**
1. Test tag classification logic - `test/unit/app/stats/tag_classifier_spec.spl`
2. Test doc coverage aggregation - `test/unit/app/stats/doc_coverage_spec.spl`
3. Test compiler warnings - `test/unit/app/build/doc_warnings_spec.spl`
4. Test JSON export - `test/unit/app/stats/json_export_spec.spl`
5. Integration tests - full pipeline from source to JSON

**Output:**
- 80+ unit tests
- Integration tests passing
- Edge cases covered

---

### Phase 5: Documentation (Docs Agent)
**Duration:** 1 hour
**Files:** 3-4 markdown files

**Tasks:**
1. Update `doc/guide/documentation_coverage.md` - comprehensive guide
2. Create `doc/design/tag_taxonomy.md` - tag reference
3. Update `CLAUDE.md` - new CLI flags
4. Update `README.md` - add coverage badges/stats

**Output:**
- User-facing documentation
- Developer guide for extending tags
- Examples and best practices

---

### Phase 6: CI/CD Integration (Infra Agent)
**Duration:** 1 hour
**Files:** 2-3 CI config files

**Tasks:**
1. Add doc coverage check to CI pipeline
2. Generate coverage trends over time
3. Fail builds below threshold
4. Upload JSON artifacts

**Output:**
- Automated coverage tracking
- Historical trend data
- Quality gate enforcement

---

## Tag Naming Standards

### Category Prefixes

**Status Tags:**
- `doc_status:*` - Documentation completeness level
- `sdoctest:*` - SDoctest coverage quality
- `group_comment:*` - Group comment presence

**Classification Tags:**
- `visibility:*` - API visibility level
- `item_kind:*` - Type of code item
- `module:*` - Module category
- `var_group:*` - Variable group pattern

**Priority Tags:**
- `priority:*` - Urgency of documentation need

**Quality Tags:**
- `quality:*` - Overall documentation quality (future)

### Tag Format Rules

1. **Lowercase only** - `doc_status:complete` not `doc_status:Complete`
2. **Colon separator** - `category:value`
3. **Underscore for multi-word** - `doc_status` not `docstatus`
4. **Descriptive values** - `missing` not `no` or `0`
5. **Consistent hierarchy** - always `category:subcategory:detail`

---

## Threshold Configuration

### Default Thresholds

```sdn
{
  doc_coverage_thresholds: {
    public_documented: 80,      # 80% of public items must have docs
    public_sdoctest: 60,        # 60% of public functions need examples
    inline_comment: 70,         # 70% of items need inline comments
    group_comment: 50           # 50% of var groups need comments
  },

  warning_levels: {
    public_missing_docs: "error",
    public_missing_sdoctest: "warn",
    internal_missing_docs: "info",
    missing_group_comment: "note"
  },

  quality_gates: {
    fail_build_on_critical: true,
    fail_build_on_threshold: false,
    emit_warnings_always: true
  }
}
```

**Configuration File:** `simple.doc_coverage.sdn`

---

## Example Workflows

### Workflow 1: Check Documentation Coverage

```bash
# Quick overview
simple stats --doc-coverage

# Detailed breakdown
simple stats --doc-coverage --verbose

# JSON export for CI
simple stats --doc-coverage --json > coverage.json

# Inline comment analysis
simple stats --inline-coverage

# Group comment analysis
simple stats --group-coverage
```

### Workflow 2: Build with Doc Warnings

```bash
# Standard build with warnings
simple build --warn-docs

# Treat warnings as errors
simple build --warn-docs=error

# Only show critical issues
simple build --warn-docs=critical

# Enforce 80% threshold
simple build --doc-threshold=80
```

### Workflow 3: Tag-Based Filtering

```bash
# Find all items missing sdoctest
simple stats --filter-tag=sdoctest:missing

# Find critical priority items
simple stats --filter-tag=priority:critical

# Find stdlib functions needing docs
simple stats --filter-tag=module:stdlib --filter-tag=doc_status:missing
```

---

## Success Metrics

**Phase 1-2 Complete:**
- ✅ JSON export includes all metrics
- ✅ Build integration working
- ✅ Tag classification system operational

**Phase 3-4 Complete:**
- ✅ 80+ tests passing
- ✅ Statistics command enhanced
- ✅ All coverage types tracked

**Phase 5-6 Complete:**
- ✅ Documentation complete
- ✅ CI/CD integrated
- ✅ Quality gates enforcing standards

**Final State:**
- 📊 Real-time documentation coverage tracking
- 🏷️ Hierarchical tag taxonomy
- ⚠️ Compiler warnings for missing docs
- 📈 Trend analysis over time
- 🚦 Automated quality gates

---

## Future Enhancements

1. **AI-Powered Suggestions**
   - Generate draft docstrings from function signatures
   - Suggest sdoctest examples based on function behavior

2. **Interactive HTML Report**
   - Clickable coverage dashboard
   - Per-file drill-down
   - Tag filtering and search

3. **LSP Integration**
   - Real-time doc warnings in editor
   - Quick-fix suggestions
   - Inline coverage indicators

4. **Documentation Debt Tracking**
   - Track tech debt over time
   - Prioritize documentation work
   - Gamification/leaderboards

---

## Agent Coordination

**Primary Agents:**
1. **Code Agent** - Core implementation (Phases 1, 3)
2. **Infra Agent** - Build/CI integration (Phases 2, 6)
3. **Test Agent** - Testing suite (Phase 4)
4. **Docs Agent** - Documentation (Phase 5)

**Communication:**
- Phase handoffs via status reports
- Shared data structures (DocItem, tags)
- JSON schema as contract

**Timeline:**
- **Total Duration:** 8-10 hours
- **Parallelizable:** Phases 1+5, 2+4, 3+6
- **Sequential:** 1→2→3, 4 after 1-3, 5+6 anytime

---

## Conclusion

This design provides a comprehensive documentation coverage system that:
- ✅ Tracks all doc types (inline, docstring, sdoctest, group)
- ✅ Uses hierarchical tagging for classification
- ✅ Integrates into build pipeline
- ✅ Provides actionable warnings
- ✅ Exports machine-readable metrics
- ✅ Enforces quality standards

Implementation via multi-agent coordination ensures clean separation of concerns and parallel development.
