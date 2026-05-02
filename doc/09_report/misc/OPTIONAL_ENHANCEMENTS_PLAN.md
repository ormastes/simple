# Optional Enhancements - Implementation Plan

## Overview
Implement 5 optional enhancements for Public API SDoctest enforcement (~460 lines total)

## Phase 1: CLI Integration (~150 lines)

### Files to Create/Modify

1. **`src/app/cli/doc_coverage_command.spl`** (NEW - 80 lines)
   - `fn doc_coverage_command(args: [text]) -> i64`
   - Parse flags: `--check-public-api`, `--missing`, `--format`
   - Call init_parser and generate reports
   - Return exit code (0 = success, 1 = missing coverage)

2. **`src/app/cli/main.spl`** (MODIFY - add 20 lines)
   - Add "doc-coverage" command handler
   - Wire to doc_coverage_command()

3. **`src/app/build/doc_warnings.spl`** (MODIFY - add 50 lines)
   - `fn check_public_api_coverage() -> [text]`
   - Parse all __init__.spl files
   - Generate warning messages
   - Called from build with `--enforce-public-sdoctest`

### Implementation Order
1. Create doc_coverage_command.spl
2. Update cli/main.spl
3. Enhance build/doc_warnings.spl

---

## Phase 2: Coverage Reporting (~100 lines)

### Files to Create/Modify

1. **`src/app/stats/doc_coverage.spl`** (MODIFY - add 60 lines)
   - `fn compute_public_api_stats() -> PublicApiStats`
   - Count total groups/items, covered, missing
   - Calculate coverage %
   - Return struct with metrics

2. **`src/app/stats/types.spl`** (MODIFY - add 15 lines)
   - Add `PublicApiStats` struct
   - Fields: total_groups, covered_groups, total_items, covered_items, coverage_pct

3. **`src/app/doc_coverage/reporting/terminal_renderer.spl`** (MODIFY - add 25 lines)
   - `fn render_public_api_section(stats: PublicApiStats)`
   - Display coverage % with color coding
   - List missing groups/items

### Implementation Order
1. Add PublicApiStats to types.spl
2. Implement compute_public_api_stats()
3. Update terminal_renderer.spl

---

## Phase 3: Build Warnings (~80 lines)

### Files to Create/Modify

1. **`src/app/doc_coverage/compiler_warnings.spl`** (MODIFY - add 50 lines)
   - `fn generate_public_api_warnings() -> [text]`
   - For each missing group: format warning with file/line
   - For each missing item: format warning
   - Return array of warning messages

2. **`src/app/build/main.spl`** (MODIFY - add 30 lines)
   - Check for `--warn-docs` flag
   - Call generate_public_api_warnings()
   - Print warnings to stderr
   - Continue build (don't fail)

### Implementation Order
1. Add warning generator to compiler_warnings.spl
2. Integrate into build/main.spl

---

## Phase 4: Threshold System (~70 lines)

### Files to Create/Modify

1. **`src/app/doc_coverage/thresholds/types.spl`** (MODIFY - add 20 lines)
   - Add fields to ThresholdConfig:
     - `public_api_group_threshold: i64` (default 80)
     - `public_api_item_threshold: i64` (default 90)
     - `enforce_at_build: bool` (default false)

2. **`src/app/doc_coverage/thresholds/config_parser.spl`** (MODIFY - add 25 lines)
   - Parse new fields from doc_coverage.sdn
   - Set defaults if not specified

3. **`src/app/doc_coverage/thresholds/validator.spl`** (MODIFY - add 25 lines)
   - `fn validate_public_api_coverage(stats: PublicApiStats, config: ThresholdConfig) -> bool`
   - Check coverage % against thresholds
   - Return true if passing, false if failing

### Implementation Order
1. Update types.spl with new fields
2. Add parsing logic to config_parser.spl
3. Implement validator logic

---

## Phase 5: Auto-Tagging (~60 lines)

### Files to Create/Modify

1. **`src/app/doc_coverage/tagging/tag_generator.spl`** (MODIFY - add 40 lines)
   - `fn generate_public_api_tags(groups: [PublicApiGroup], items: [PublicApiItem]) -> [TagSuggestion]`
   - For grouped items: suggest `@tag:api-grouped`
   - For non-grouped: suggest `@tag:api-individual`
   - Return list of suggestions

2. **`src/app/doc_coverage/scanner/file_scanner.spl`** (MODIFY - add 20 lines)
   - After scanning, call generate_public_api_tags()
   - Merge tags into DocItem records
   - Update is_public field

### Implementation Order
1. Add tag generation logic to tag_generator.spl
2. Integrate into file_scanner.spl

---

## Testing Plan

### New Test Files

1. **`test/unit/app/cli/doc_coverage_command_spec.spl`** (~40 lines)
   - Test CLI argument parsing
   - Test exit codes
   - Test format options

2. **`test/unit/app/stats/public_api_stats_spec.spl`** (~30 lines)
   - Test stats computation
   - Test coverage % calculation

3. **`test/unit/app/doc_coverage/public_api_warnings_spec.spl`** (~30 lines)
   - Test warning generation
   - Test message formatting

4. **`test/unit/app/doc_coverage/public_api_thresholds_spec.spl`** (~30 lines)
   - Test threshold validation
   - Test config parsing

5. **`test/unit/app/doc_coverage/public_api_tagging_spec.spl`** (~30 lines)
   - Test tag generation
   - Test tag suggestions

**Total test lines:** ~160 lines

---

## Implementation Order (All Phases)

### Step 1: Foundations
- Add types (PublicApiStats, ThresholdConfig updates)
- ~35 lines

### Step 2: Core Logic
- compute_public_api_stats()
- generate_public_api_warnings()
- generate_public_api_tags()
- ~150 lines

### Step 3: Integration Points
- CLI command handler
- Build integration
- Stats integration
- Scanner integration
- ~130 lines

### Step 4: Threshold System
- Config parsing
- Validation logic
- ~50 lines

### Step 5: Reporting
- Terminal rendering
- Format options
- ~25 lines

### Step 6: Tests
- 5 test files
- ~160 lines

**Total: ~550 lines** (including tests)

---

## Config File Example

```sdn
# doc_coverage.sdn
public_api_group_threshold: 80
public_api_item_threshold: 90
enforce_at_build: false
warn_on_missing: true
auto_tag_public_api: true
```

---

## Success Criteria

- [ ] `bin/simple doc-coverage --check-public-api` works
- [ ] `bin/simple stats` shows public API coverage %
- [ ] `bin/simple build --warn-docs` shows warnings
- [ ] Threshold validation works with doc_coverage.sdn
- [ ] Auto-tagging generates correct suggestions
- [ ] All tests pass (5 new test files)
- [ ] Exit codes work correctly (0 = pass, 1 = fail)
- [ ] Documentation updated

---

## Time Estimate

- Phase 1 (CLI): 30 min
- Phase 2 (Reporting): 25 min
- Phase 3 (Warnings): 20 min
- Phase 4 (Thresholds): 20 min
- Phase 5 (Tagging): 15 min
- Testing: 30 min
- **Total: ~2.5 hours**
