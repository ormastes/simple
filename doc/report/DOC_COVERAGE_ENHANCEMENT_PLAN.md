# Documentation Coverage Enhancement Plan
**Date:** 2026-02-14
**Status:** Implementation Phase
**Agents:** docs (design), code (implementation), test (validation), infra (integration)

---

## Current Status Assessment

### ✅ Already Implemented (Foundation)
- **Types:** `DocItem`, `DocKind` structs with all needed fields
- **Analysis Modules:**
  - `sdoctest_coverage.spl` - SDoctest block extraction and matching
  - `inline_comment_coverage.spl` - Inline comment detection
  - `group_comment_detection.spl` - Variable group detection
  - `export_parser.spl` - Public API detection from `__init__.spl`/`mod.spl`
  - `compiler_warnings.spl` - Basic warning generation
- **Scanner:** File discovery, doc item extraction
- **Stats:** Basic integration in `dynamic.spl`
- **Tests:** Skeleton test files exist

### 🔧 Needs Enhancement

#### 1. Statistics System Enhancement
**Goal:** Comprehensive metrics in `simple stats` command

**Current:** Basic file/line counts
**Target:** Full doc coverage metrics with breakdown by scope

**Tasks:**
- Integrate doc coverage into stats collection
- Add public vs internal function counts
- Calculate sdoctest coverage percentage
- Calculate inline comment coverage percentage
- Group comment coverage metrics
- Per-scope breakdown (std/, core/, lib/, app/)
- Trend tracking (optional)

**Files to Modify:**
- `src/app/stats/dynamic.spl` - Add doc coverage metrics
- `src/app/stats/types.spl` - Add coverage result types
- `src/app/stats/json_formatter.spl` - Export coverage JSON

#### 2. Tag System Implementation
**Goal:** Auto-tag functions/modules based on documentation status

**Tag Schema:**
```
# Coverage Level Tags (auto-generated from percentage)
coverage:excellent     # ≥95% coverage
coverage:good          # 80-94%
coverage:acceptable    # 60-79%
coverage:poor          # 40-59%
coverage:insufficient  # <40%

# Documentation Status Tags
doc:missing_sdoctest          # Public function lacks sdoctest
doc:missing_inline_comment    # No inline comment
doc:missing_group_comment     # Variable group undocumented
doc:complete                  # Has all required documentation
doc:incomplete                # Partial documentation

# Scope Tags (auto-generated from file path)
scope:stdlib      # src/std/
scope:core        # src/compiler_core/
scope:lib         # src/lib/
scope:app         # src/app/
scope:compiler    # src/compiler/

# Public API Tags
api:public        # Exported in __init__.spl/mod.spl
api:internal      # Not exported
```

**Tasks:**
- Create tag generation functions
- Tag validation/normalization
- Output tags in statistics report
- CLI flag to show only items with specific tags

**Files to Create:**
- `src/app/doc_coverage/tagging/tag_generator.spl`
- `src/app/doc_coverage/tagging/tag_validator.spl`

#### 3. Compiler Warning Integration
**Goal:** Warnings during `simple build` for missing docs

**Current:** Basic warning generation exists
**Target:** Full integration with build system

**Tasks:**
- Add CLI flags: `--warn-docs`, `--warn-docs-level=warn|error`, `--warn-docs-fail-on-error`
- Wire into build system (`src/app/build/orchestrator.spl`)
- Format warnings nicely (file:line:col format)
- Support warning suppression (per-file or per-function)
- Count and report warning summary at end

**Files to Modify:**
- `src/app/cli/main.spl` - Add CLI flags
- `src/app/build/orchestrator.spl` - Call doc checker
- `src/app/doc_coverage/compiler_warnings.spl` - Enhance warning format

#### 4. Enhanced Reporting System
**Goal:** Multiple output formats for CI/CD and tooling

**Formats:**
1. **JSON** - Machine-readable for CI/CD
2. **CSV** - Import into spreadsheets
3. **Markdown** - Human-readable reports
4. **Terminal** - Colorized table output

**Report Contents:**
- Summary: total items, coverage %, missing docs count
- Per-scope breakdown: std/, core/, lib/, app/, compiler/
- Top 10 files needing documentation
- Functions missing sdoctests (with file:line)
- Variable groups missing comments
- Trend: coverage change over time (if historical data exists)

**Tasks:**
- Create report generator module
- JSON export with full detail
- CSV export (flat structure)
- Markdown report template
- Terminal colorized output (with emoji indicators)

**Files to Create:**
- `src/app/doc_coverage/reporting/json_exporter.spl`
- `src/app/doc_coverage/reporting/csv_exporter.spl`
- `src/app/doc_coverage/reporting/markdown_generator.spl`
- `src/app/doc_coverage/reporting/terminal_renderer.spl`

#### 5. Threshold System
**Goal:** Enforce minimum coverage requirements per scope

**Config File:** `doc_coverage.sdn`
```sdn
doc_coverage {
    default_threshold 70

    thresholds {
        "src/std/" 90
        "src/compiler_core/" 75
        "src/lib/" 80
        "src/app/" 50
        "src/compiler/" 60
    }

    enforce true
    fail_on_below_threshold false

    exclude [
        "test/**"
        "**/deprecated/**"
    ]
}
```

**Tasks:**
- Parse `doc_coverage.sdn` config
- Calculate coverage per scope
- Compare against thresholds
- Generate threshold report (pass/fail per scope)
- CLI flag `--fail-on-below-threshold` for CI

**Files to Create:**
- `src/app/doc_coverage/thresholds/config_parser.spl`
- `src/app/doc_coverage/thresholds/calculator.spl`
- `src/app/doc_coverage/thresholds/validator.spl`

#### 6. CLI Commands Enhancement
**Goal:** Rich CLI interface for doc coverage

**Commands:**
```bash
# Statistics with doc coverage
simple stats                              # Include doc coverage in output
simple stats --doc-coverage-only          # Show only doc coverage
simple stats --format=json                # JSON export
simple stats --format=csv                 # CSV export
simple stats --scope=src/std/             # Filter by scope

# Documentation coverage standalone
simple doc-coverage                       # Full report
simple doc-coverage --missing             # Show only missing docs
simple doc-coverage --thresholds          # Check against thresholds
simple doc-coverage --tag=scope:stdlib    # Filter by tag
simple doc-coverage --export=report.md    # Export markdown report

# Build with warnings
simple build --warn-docs                  # Enable doc warnings
simple build --warn-docs-level=error      # Treat as errors
simple build --warn-docs-fail-on-error    # Exit 1 on warnings
```

**Files to Modify:**
- `src/app/cli/main.spl` - Add commands and flags
- `src/app/cli/doc_coverage_command.spl` - New command handler (create)

---

## Implementation Phases

### Phase 1: Enhanced Statistics (Agent: code)
**Duration:** 2-3 hours
**Priority:** HIGH

1. Integrate doc coverage into `src/app/stats/dynamic.spl`
2. Add coverage metrics calculation
3. Update JSON formatter to include coverage
4. Test with `simple stats`

**Acceptance:**
- `simple stats` shows doc coverage metrics
- JSON export includes coverage data
- Public vs internal function counts accurate

### Phase 2: Tag System (Agent: code)
**Duration:** 2-3 hours
**Priority:** HIGH

1. Create tag generator module
2. Implement tag validation
3. Add tags to DocItem
4. Output tags in reports

**Acceptance:**
- Functions auto-tagged based on coverage level
- Tags follow naming convention
- `simple stats --format=json` includes tags

### Phase 3: Compiler Integration (Agent: code + infra)
**Duration:** 3-4 hours
**Priority:** MEDIUM

1. Add CLI flags for `--warn-docs*`
2. Wire into build orchestrator
3. Enhance warning format
4. Test with real builds

**Acceptance:**
- `simple build --warn-docs` emits warnings
- Warnings show file:line:col
- `--warn-docs-fail-on-error` exits with error code

### Phase 4: Reporting System (Agent: code)
**Duration:** 4-5 hours
**Priority:** MEDIUM

1. Create JSON exporter
2. Create CSV exporter
3. Create Markdown generator
4. Create terminal renderer (colorized)

**Acceptance:**
- `simple stats --format=json` exports full JSON
- `simple stats --format=csv` exports flat CSV
- Markdown report is human-readable
- Terminal output uses colors/emojis

### Phase 5: Threshold System (Agent: code + infra)
**Duration:** 3-4 hours
**Priority:** LOW

1. Create SDN config parser
2. Implement threshold calculator
3. Add threshold validation
4. CLI command for threshold checking

**Acceptance:**
- `doc_coverage.sdn` config parsed correctly
- `simple doc-coverage --thresholds` shows pass/fail
- `--fail-on-below-threshold` exits with error

### Phase 6: Testing (Agent: test)
**Duration:** 4-5 hours
**Priority:** HIGH (run in parallel with implementation)

1. Write tests for tag system
2. Write tests for statistics integration
3. Write tests for reporting formats
4. Write tests for threshold system
5. Integration tests for CLI commands

**Acceptance:**
- 100% test coverage for new modules
- All existing tests still pass
- Edge cases covered (empty files, no docs, etc.)

### Phase 7: Documentation (Agent: docs)
**Duration:** 2-3 hours
**Priority:** MEDIUM

1. Update `CLAUDE.md` with new commands
2. Create user guide: `doc/guide/doc_coverage.md`
3. Update design docs with implementation details
4. Add examples to README

**Acceptance:**
- User guide explains all features
- Examples demonstrate usage
- CLAUDE.md has command reference

---

## Agent Assignments

### Agent 1: docs (Design & Documentation)
**Tasks:**
- Review and refine tag naming scheme
- Create comprehensive design document
- Write user guide
- Create examples

**Deliverables:**
- `doc/design/doc_coverage_complete_design.md`
- `doc/guide/doc_coverage_user_guide.md`
- Updated `CLAUDE.md`

### Agent 2: code (Statistics & Tagging)
**Tasks:**
- Integrate doc coverage into stats system
- Implement tag generation and validation
- Add coverage metrics calculation
- Enhance JSON/CSV export

**Deliverables:**
- Enhanced `src/app/stats/dynamic.spl`
- New `src/app/doc_coverage/tagging/` modules
- Working `simple stats` with doc coverage

### Agent 3: code (Reporting & CLI)
**Tasks:**
- Create reporting modules (JSON, CSV, Markdown, Terminal)
- Add CLI commands and flags
- Integrate with build system
- Wire up compiler warnings

**Deliverables:**
- `src/app/doc_coverage/reporting/` modules
- Enhanced `src/app/cli/main.spl`
- New `src/app/cli/doc_coverage_command.spl`

### Agent 4: code (Thresholds)
**Tasks:**
- Implement SDN config parser
- Create threshold calculator
- Add validation logic
- CLI integration

**Deliverables:**
- `src/app/doc_coverage/thresholds/` modules
- Threshold checking command
- `doc_coverage.sdn` template

### Agent 5: test (Validation)
**Tasks:**
- Write comprehensive test suite
- Test all new modules
- Integration testing
- Edge case coverage

**Deliverables:**
- Test files in `test/unit/app/doc_coverage/`
- Test files in `test/unit/app/stats/`
- All tests passing

### Agent 6: infra (Integration)
**Tasks:**
- Wire into build system
- Integrate with CLI dispatcher
- Add to CI/CD pipeline
- Verify end-to-end workflow

**Deliverables:**
- Working integration in build
- CI checks for doc coverage
- End-to-end testing

---

## Success Metrics

1. **Coverage:** `simple stats` shows ≥90% doc coverage for `src/std/`
2. **Warnings:** `simple build --warn-docs` shows all undocumented public functions
3. **Reporting:** `simple stats --format=json` exports complete coverage data
4. **Thresholds:** Threshold system catches below-threshold modules
5. **Tests:** 100% test coverage for new modules, all tests passing
6. **Documentation:** Complete user guide with examples

---

## Execution Plan

**Parallel Execution Strategy:**
- Run Agents 1, 2, 3, 4, 5 in parallel (independent work)
- Agent 6 runs after Agents 2, 3, 4 complete (depends on integration points)

**Timeline:**
- Phase 1-2: Hours 0-4 (parallel)
- Phase 3-4: Hours 4-8 (parallel)
- Phase 5: Hours 8-11
- Phase 6: Hours 0-11 (parallel throughout)
- Phase 7: Hours 11-13

**Total Estimated Time:** ~13 hours of agent work (with parallelization: ~6-7 hours wall clock time)

---

## Next Steps

1. Spawn Agent 1 (docs) - Design refinement and tag scheme
2. Spawn Agent 2 (code) - Statistics integration
3. Spawn Agent 3 (code) - Reporting and CLI
4. Spawn Agent 4 (code) - Thresholds
5. Spawn Agent 5 (test) - Comprehensive testing
6. Spawn Agent 6 (infra) - Integration (after 2, 3, 4 complete)
