# Documentation Coverage Multi-Agent Implementation Plan
**Date:** 2026-02-14
**Design:** `doc_coverage_enhancements_2026-02-14.md`
**Coordination:** 4 agents in 6 phases

## Agent Roles & Responsibilities

### Code Agent
**Expertise:** Simple language implementation, data structures, algorithms
**Responsibilities:**
- Core feature implementation
- Data aggregation pipelines
- Tag classification logic
- Statistics computation

**Files Owned:**
- `src/app/stats/doc_coverage.spl`
- `src/app/stats/tag_classifier.spl`
- `src/app/stats/types.spl` (extensions)
- `src/app/stats/dynamic.spl` (enhancements)

---

### Infra Agent
**Expertise:** Build systems, compiler integration, FFI, I/O operations
**Responsibilities:**
- Build pipeline integration
- Compiler warning hooks
- File I/O and caching
- CI/CD setup

**Files Owned:**
- `src/app/build/orchestrator.spl` (doc check hooks)
- `src/app/build/config.spl` (new flags)
- `src/app/doc_coverage/compiler_warnings.spl` (threshold checking)
- CI/CD configs

---

### Test Agent
**Expertise:** SSpec framework, test coverage, edge case detection
**Responsibilities:**
- Unit test suites
- Integration tests
- Fixture creation
- Coverage verification

**Files Owned:**
- `test/unit/app/stats/tag_classifier_spec.spl`
- `test/unit/app/stats/doc_coverage_spec.spl`
- `test/unit/app/build/doc_warnings_spec.spl`
- `test/fixtures/doc_coverage/*`

---

### Docs Agent
**Expertise:** Technical writing, markdown, user guides
**Responsibilities:**
- User-facing documentation
- Design documentation
- API reference
- Example creation

**Files Owned:**
- `doc/guide/documentation_coverage.md`
- `doc/design/tag_taxonomy.md`
- `CLAUDE.md` (updates)
- `README.md` (updates)

---

## Phase-by-Phase Execution

### Phase 1: Foundation (Code Agent)
**Duration:** 2 hours
**Dependencies:** None
**Deliverables:** 3-5 new modules

#### Tasks

**1.1 Create Tag Classifier Module**
```
File: src/app/stats/tag_classifier.spl
Lines: ~250
Functions:
  - classify_doc_item(item: DocItem) -> [text]
  - infer_module_tag(file_path: text) -> text
  - count_sdoctest_examples(func_name: text) -> i64
  - compute_priority(item: DocItem) -> text
```

**1.2 Create Doc Coverage Aggregator**
```
File: src/app/stats/doc_coverage.spl
Lines: ~350
Functions:
  - aggregate_doc_coverage(files: [text]) -> DocCoverageStats
  - compute_by_kind_stats(items: [DocItem]) -> [(text, KindStats)]
  - compute_by_module_stats(items: [DocItem]) -> [(text, ModuleStats)]
  - find_missing_sdoctest(items: [DocItem], blocks: [text]) -> [text]
```

**1.3 Extend Types Module**
```
File: src/app/stats/types.spl (modifications)
Lines: +150
Structs:
  - DocCoverageStats
  - KindStats
  - ModuleStats
  - InlineCommentStats
  - GroupCommentStats
```

**1.4 Extend JSON Formatter**
```
File: src/app/stats/json_formatter.spl (modifications)
Lines: +200
Functions:
  - format_doc_coverage_json(stats: DocCoverageStats) -> text
  - format_inline_coverage_json(stats: InlineCommentStats) -> text
  - format_group_coverage_json(stats: GroupCommentStats) -> text
```

#### Acceptance Criteria
- [ ] All tag categories implemented (doc_status, sdoctest, visibility, etc.)
- [ ] Aggregation computes all metrics correctly
- [ ] JSON export includes all fields from design
- [ ] Unit tests for tag classification (Phase 4 dependency)

#### Output Artifacts
- `tag_classifier.spl` - ready for testing
- `doc_coverage.spl` - aggregation pipeline complete
- `types.spl` - extended with new structs
- `json_formatter.spl` - enhanced export

---

### Phase 2: Compiler Integration (Infra Agent)
**Duration:** 1.5 hours
**Dependencies:** Phase 1 complete
**Deliverables:** 2-3 modified modules

#### Tasks

**2.1 Add Build Flags**
```
File: src/app/build/config.spl (modifications)
Lines: +50
Additions:
  - warn_docs: bool
  - warn_docs_level: text  # "error", "warn", "info", "note"
  - doc_threshold: i64
  - Parse --warn-docs, --warn-docs=error, --doc-threshold=80
```

**2.2 Hook into Build Orchestrator**
```
File: src/app/build/orchestrator.spl (modifications)
Lines: +100
Additions:
  - check_documentation_coverage(files: [text], config: BuildConfig) -> bool
  - emit_doc_warnings(warnings: [text], level: text)
  - enforce_thresholds(stats: DocCoverageStats, threshold: i64) -> bool
  - Called after successful compilation, before test run
```

**2.3 Threshold Checking**
```
File: src/app/doc_coverage/compiler_warnings.spl (modifications)
Lines: +80
Functions:
  - check_threshold(stats: DocCoverageStats, min_percent: i64) -> (bool, text)
  - format_threshold_failure(stats: DocCoverageStats, min: i64) -> text
```

**2.4 Warning Output Format**
```
Example output:
warning[doc-missing]: missing documentation for function `parse_expr`
  --> src/core/parser.spl:145
  |
145| fn parse_expr():
  |    ^^^^^^^^^^
  |
  = help: add inline comment and docstring
  = help: add sdoctest example in doc/guide/parsing.md
```

#### Acceptance Criteria
- [ ] `--warn-docs` flag recognized
- [ ] Warnings emitted during build
- [ ] Threshold enforcement works
- [ ] Build fails when threshold violated (if configured)
- [ ] Warning format matches design

#### Output Artifacts
- Modified `config.spl` - new flags parsed
- Modified `orchestrator.spl` - doc checking integrated
- Enhanced `compiler_warnings.spl` - threshold logic

---

### Phase 3: Statistics Enhancement (Code Agent)
**Duration:** 2 hours
**Dependencies:** Phase 1 complete
**Deliverables:** 4-5 modified modules

#### Tasks

**3.1 Extend Stats Dynamic Module**
```
File: src/app/stats/dynamic.spl (major refactor)
Lines: +300
Functions:
  - compute_full_doc_coverage() -> DocCoverageStats
  - compute_inline_coverage() -> InlineCommentStats
  - compute_group_coverage() -> GroupCommentStats
  - aggregate_all_coverage() -> ComprehensiveCoverageReport
  - format_coverage_report(report: ComprehensiveCoverageReport, flags: [text])
```

**3.2 Add CLI Flags**
```
New flags:
  --doc-coverage          # Show detailed doc coverage
  --inline-coverage       # Show inline comment analysis
  --group-coverage        # Show group comment analysis
  --filter-tag=TAG        # Filter by tag
  --coverage-trend        # Compare to previous run
```

**3.3 Detailed Report Formatting**
```
File: src/app/stats/formatter.spl (modifications)
Lines: +200
Functions:
  - format_doc_coverage_table(stats: DocCoverageStats) -> text
  - format_by_kind_table(kind_stats: [(text, KindStats)]) -> text
  - format_by_module_table(module_stats: [(text, ModuleStats)]) -> text
  - format_missing_items_list(items: [text]) -> text
```

**3.4 Trend Tracking**
```
File: src/app/stats/trend_tracker.spl (new)
Lines: ~200
Functions:
  - save_coverage_snapshot(stats: DocCoverageStats, timestamp: i64)
  - load_previous_snapshot() -> DocCoverageStats
  - compute_trend_delta(current: DocCoverageStats, previous: DocCoverageStats) -> TrendDelta
  - format_trend_report(delta: TrendDelta) -> text
```

#### Acceptance Criteria
- [ ] All coverage types computed correctly
- [ ] CLI flags working
- [ ] Reports formatted clearly
- [ ] Trend tracking operational
- [ ] Filter by tag works

#### Output Artifacts
- Refactored `dynamic.spl` - comprehensive coverage
- Enhanced `formatter.spl` - beautiful reports
- New `trend_tracker.spl` - historical analysis

---

### Phase 4: Testing (Test Agent)
**Duration:** 2 hours
**Dependencies:** Phases 1-3 complete
**Deliverables:** 6-8 test files, 80+ tests

#### Tasks

**4.1 Tag Classifier Tests**
```
File: test/unit/app/stats/tag_classifier_spec.spl
Tests: ~20
Coverage:
  - classify_doc_item() with various doc states
  - infer_module_tag() for all module types
  - count_sdoctest_examples() edge cases
  - compute_priority() logic
```

**4.2 Doc Coverage Tests**
```
File: test/unit/app/stats/doc_coverage_spec.spl
Tests: ~25
Coverage:
  - aggregate_doc_coverage() full pipeline
  - compute_by_kind_stats() all item kinds
  - compute_by_module_stats() all modules
  - find_missing_sdoctest() accuracy
```

**4.3 Compiler Warnings Tests**
```
File: test/unit/app/build/doc_warnings_spec.spl
Tests: ~15
Coverage:
  - check_threshold() pass/fail cases
  - emit_doc_warnings() format correctness
  - Warning level filtering
```

**4.4 JSON Export Tests**
```
File: test/unit/app/stats/json_export_spec.spl
Tests: ~12
Coverage:
  - format_doc_coverage_json() schema compliance
  - format_inline_coverage_json() completeness
  - Nested structures correct
  - Valid JSON parsing
```

**4.5 Integration Tests**
```
File: test/integration/doc_coverage_pipeline_spec.spl
Tests: ~8
Coverage:
  - End-to-end: source files → coverage stats → JSON
  - Build integration: compile + doc check
  - Threshold enforcement
  - Warning emission
```

**4.6 Fixtures**
```
Files: test/fixtures/doc_coverage/*
Contents:
  - sample_documented.spl (fully documented)
  - sample_partial.spl (partial docs)
  - sample_missing.spl (no docs)
  - sample_group_comments.spl (var groups)
  - expected_tags.json (tag classification results)
```

#### Acceptance Criteria
- [ ] 80+ tests written
- [ ] All core logic covered
- [ ] Integration tests passing
- [ ] Fixtures comprehensive
- [ ] Edge cases tested

#### Output Artifacts
- 6 test spec files
- Comprehensive fixture library
- Test coverage report

---

### Phase 5: Documentation (Docs Agent)
**Duration:** 1 hour
**Dependencies:** Phases 1-3 complete (can run parallel to Phase 4)
**Deliverables:** 3-4 documentation files

#### Tasks

**5.1 User Guide**
```
File: doc/guide/documentation_coverage.md
Sections:
  - Overview of coverage system
  - How to check coverage (simple stats --doc-coverage)
  - How to improve coverage (adding docs, sdoctest)
  - Tag taxonomy reference
  - Threshold configuration
  - CI/CD integration examples
```

**5.2 Tag Taxonomy Reference**
```
File: doc/design/tag_taxonomy.md
Sections:
  - Tag hierarchy (doc_status, sdoctest, visibility, etc.)
  - Tag assignment logic
  - Priority classification
  - Examples for each tag category
  - How to filter by tags
```

**5.3 CLAUDE.md Updates**
```
File: CLAUDE.md
Additions:
  - New CLI flags (--warn-docs, --doc-coverage, etc.)
  - Quick commands section
  - Tag filtering examples
```

**5.4 README.md Updates**
```
File: README.md
Additions:
  - Documentation coverage badge (if applicable)
  - Link to coverage guide
  - Quick example of checking coverage
```

#### Acceptance Criteria
- [ ] User guide comprehensive
- [ ] Tag reference complete
- [ ] Examples runnable
- [ ] Links between docs correct
- [ ] Markdown rendering correct

#### Output Artifacts
- `documentation_coverage.md` - user guide
- `tag_taxonomy.md` - reference
- Updated `CLAUDE.md` and `README.md`

---

### Phase 6: CI/CD Integration (Infra Agent)
**Duration:** 1 hour
**Dependencies:** Phases 1-3 complete
**Deliverables:** CI/CD configs

#### Tasks

**6.1 GitHub Actions Workflow**
```
File: .github/workflows/doc-coverage.yml
Jobs:
  - check-coverage:
      - Checkout code
      - Run: simple stats --doc-coverage --json > coverage.json
      - Upload artifact: coverage.json
      - Check threshold: fail if < 80%
  - track-trends:
      - Download previous coverage.json
      - Compare current to previous
      - Post comment on PR with delta
```

**6.2 Coverage Threshold Configuration**
```
File: simple.doc_coverage.sdn (new)
Contents:
  doc_coverage_thresholds: {
    public_documented: 80,
    public_sdoctest: 60,
    inline_comment: 70,
    group_comment: 50
  }
  warning_levels: { ... }
  quality_gates: { ... }
```

**6.3 Badge Generation Script**
```
File: scripts/generate-coverage-badge.sh
Purpose:
  - Parse coverage.json
  - Generate SVG badge
  - Upload to shields.io or similar
```

#### Acceptance Criteria
- [ ] CI workflow runs on every push
- [ ] Coverage JSON uploaded as artifact
- [ ] Threshold violations fail PR
- [ ] Trend comparison working
- [ ] Badge updates automatically

#### Output Artifacts
- GitHub Actions workflow
- Coverage configuration
- Badge generation script

---

## Agent Communication Protocol

### Handoff Points

**Phase 1 → Phase 2:**
```
Code Agent outputs:
  - tag_classifier.spl (with exports)
  - doc_coverage.spl (with exports)
  - types.spl (with new structs)

Infra Agent imports:
  - use app.stats.tag_classifier (classify_doc_item)
  - use app.stats.doc_coverage (aggregate_doc_coverage)
  - use app.stats.types (DocCoverageStats)
```

**Phase 1 → Phase 3:**
```
Same imports as Phase 2
Additionally uses trend_tracker.spl
```

**Phases 1-3 → Phase 4:**
```
Test Agent needs:
  - All implemented modules
  - Sample input files (fixtures)
  - Expected output (tags, stats)

Test Agent verifies:
  - Public API contracts
  - Edge case handling
  - Integration correctness
```

**Phases 1-3 → Phase 5:**
```
Docs Agent documents:
  - All public functions
  - All CLI flags
  - All tag categories
  - All configuration options

Docs Agent references:
  - Source code for examples
  - Test fixtures for demonstrations
```

---

## Parallel Execution Strategy

### Stage 1 (Concurrent)
**Agents:** Code Agent (Phase 1), Docs Agent (Phase 5 - draft)
**Duration:** 2 hours
**Rationale:** Docs agent can draft user guide based on design while code implements

### Stage 2 (Concurrent)
**Agents:** Infra Agent (Phase 2), Code Agent (Phase 3)
**Duration:** 2 hours
**Rationale:** Build integration and stats enhancement are independent

### Stage 3 (Sequential)
**Agent:** Test Agent (Phase 4)
**Duration:** 2 hours
**Rationale:** Needs Phases 1-3 complete to test implementations

### Stage 4 (Concurrent)
**Agents:** Docs Agent (Phase 5 - finalize), Infra Agent (Phase 6)
**Duration:** 1 hour
**Rationale:** Both can work independently after implementation complete

**Total Wall-Clock Time:** ~5-6 hours (vs 10 hours sequential)

---

## Risk Mitigation

### Risk 1: Tag Classification Complexity
**Probability:** Medium
**Impact:** High
**Mitigation:**
  - Start with simple heuristics
  - Iteratively refine based on test results
  - Code agent owns this, test agent validates

### Risk 2: Build Integration Breaking Existing Builds
**Probability:** Low
**Impact:** High
**Mitigation:**
  - Make `--warn-docs` opt-in initially
  - Extensive testing before enabling by default
  - Feature flag in config

### Risk 3: Performance Impact on Large Codebases
**Probability:** Medium
**Impact:** Medium
**Mitigation:**
  - Cache coverage results
  - Incremental checking (only changed files)
  - Parallel file processing

### Risk 4: JSON Schema Versioning
**Probability:** Low
**Impact:** Medium
**Mitigation:**
  - Add version field to JSON output
  - Document schema changes
  - Backward compatibility for 2 versions

---

## Success Criteria

### Phase 1 Complete
- [x] Tag classification assigns correct tags (verified by unit tests)
- [x] Doc coverage aggregation computes all metrics
- [x] JSON export schema matches design
- [x] Types module extended with all structs

### Phase 2 Complete
- [x] `--warn-docs` flag recognized and working
- [x] Build emits warnings for missing docs
- [x] Threshold checking enforces quality gates
- [x] Warning format matches design spec

### Phase 3 Complete
- [x] All CLI flags working (--doc-coverage, --inline-coverage, etc.)
- [x] Reports formatted clearly and usefully
- [x] Trend tracking saves and compares snapshots
- [x] Filter by tag functionality operational

### Phase 4 Complete
- [x] 80+ tests written and passing
- [x] All core logic covered (>90% coverage)
- [x] Integration tests verify end-to-end flow
- [x] Fixtures comprehensive

### Phase 5 Complete
- [x] User guide comprehensive and clear
- [x] Tag taxonomy documented
- [x] CLAUDE.md and README.md updated
- [x] All examples runnable

### Phase 6 Complete
- [x] CI workflow running on every push
- [x] Coverage tracked over time
- [x] Threshold violations fail builds
- [x] Badges auto-updating

---

## Post-Implementation Verification

### Manual Verification Steps

1. **Run stats command:**
   ```bash
   simple stats --doc-coverage --verbose
   ```
   Verify output shows all metrics from design.

2. **Build with warnings:**
   ```bash
   simple build --warn-docs
   ```
   Verify warnings emitted for undocumented code.

3. **Threshold enforcement:**
   ```bash
   simple build --doc-threshold=100
   ```
   Verify build fails (intentionally) when threshold not met.

4. **JSON export:**
   ```bash
   simple stats --doc-coverage --json > coverage.json
   jq . coverage.json
   ```
   Verify JSON schema matches design.

5. **Tag filtering:**
   ```bash
   simple stats --filter-tag=priority:critical
   ```
   Verify only critical items shown.

### Automated Verification

Run full test suite:
```bash
simple test test/unit/app/stats/
simple test test/unit/app/build/
simple test test/integration/doc_coverage_pipeline_spec.spl
```

All tests must pass.

---

## Timeline Summary

| Phase | Agent | Duration | Dependencies | Can Parallelize |
|-------|-------|----------|--------------|-----------------|
| 1 | Code | 2h | None | With Phase 5 draft |
| 2 | Infra | 1.5h | Phase 1 | With Phase 3 |
| 3 | Code | 2h | Phase 1 | With Phase 2 |
| 4 | Test | 2h | Phases 1-3 | No |
| 5 | Docs | 1h | Phases 1-3 (draft earlier) | With Phase 6 |
| 6 | Infra | 1h | Phases 1-3 | With Phase 5 |

**Sequential Total:** 9.5 hours
**Parallel Total:** ~5-6 hours
**Efficiency Gain:** ~40%

---

## Conclusion

This multi-agent plan provides:
- ✅ Clear agent responsibilities
- ✅ Detailed task breakdowns
- ✅ Explicit handoff points
- ✅ Parallelization strategy
- ✅ Risk mitigation
- ✅ Success criteria

Implementation can begin immediately with agents working independently on their phases, coordinating at handoff points.
