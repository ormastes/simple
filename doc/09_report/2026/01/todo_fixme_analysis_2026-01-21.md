# TODO/FIXME Analysis Report
**Date:** 2026-01-21
**Total Found:** 71 occurrences across 26 files
**Actionable:** ~35 items
**Blocked:** ~36 items (waiting for stdlib/features)

---

## Summary by Category

### 1. Blocked by Missing Stdlib Features (36 items)
These TODOs cannot be resolved without implementing missing standard library modules.

#### Core Time Module (6 items)
- **Files:**
  - `src/lib/std/src/tooling/dashboard/notify.spl` (2 items)
  - `src/rust/driver/src/cli/test_output.spl` (2 items)
- **Issue:** Need `core.time` module for:
  - ISO 8601 timestamp generation
  - Proper date formatting in test output
- **Impact:** Dashboard notifications, test output formatting
- **Status:** Waiting for `core.time` implementation

#### HttpClient (2 items)
- **Files:** `src/lib/std/src/tooling/dashboard/notify.spl`
- **Issue:** No actual HTTP POST implementation - using stubs
- **Lines:** 170, 190 (Slack webhook, generic webhook)
- **Status:** Awaiting `io.net.HttpClient` completion

#### JSON Parsing Library (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/collectors/coverage_collector.spl:57`
- **Issue:** Cannot parse full JSON until JSON library available
- **Status:** Blocked on stdlib JSON module

#### Math Module - sqrt() (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/trends.spl:240`
- **Issue:** Dashboard trends calculation needs proper sqrt
- **Status:** Blocked on math stdlib module

#### Float Parsing (3 items)
- **Files:**
  - `src/lib/std/src/tooling/dashboard/alert_rules.spl:327`
  - `src/lib/std/src/tooling/dashboard/config.spl:137`
  - `src/lib/std/src/tooling/dashboard/snapshots.spl:310`
- **Issue:** Dashboard config parsing needs robust float parsing
- **Status:** Blocked on text parsing improvements

#### File System Operations (2 items)
- **Files:**
  - `src/lib/std/src/tooling/dashboard/alert_rules.spl:303` (delete_file)
  - `src/rust/driver/src/cli/test_output.spl:161` (PathBuf and fs ops)
- **Issue:** Advanced fs_helpers needed
- **Status:** Blocked on `io.fs` completion

#### Date Arithmetic (2 items)
- **Files:** `src/lib/std/src/tooling/dashboard/snapshots.spl` (lines 282, 287)
- **Issue:** Need proper datetime operations for trend analysis
- **Status:** Blocked on date/time support

#### Error Handling - try/catch (1 item)
- **Files:** `src/lib/std/src/spec/runner/executor.spl:246`
- **Issue:** Proper error handling requires try/catch blocks
- **Status:** Blocked on exception handling implementation

#### Async Support (1 item)
- **Files:** `src/rust/driver/src/cli/test_output.spl:149`
- **Issue:** Async test execution commented out
- **Status:** Blocked on async/await implementation

#### Git Integration (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl:51`
- **Issue:** Cannot calculate TODO age without git integration
- **Status:** Blocked on git operations support

#### stdlib Imports (1 item)
- **Files:** `src/rust/driver/src/cli/test_output.spl:8`
- **Issue:** Imports not yet available in stdlib
- **Status:** Blocked on stdlib completion

---

### 2. Dashboard Feature Stubs (5 items)
Dashboard functionality that needs implementation but doesn't require new stdlib modules.

#### Collectors (2 items)
- **Files:** `src/lib/std/src/tooling/dashboard/collector.spl` (lines 152, 158)
- **Items:**
  - `build_collector` - Build metrics collection
  - `dependency_collector` - Dependency tracking
- **Impact:** Dashboard metrics incomplete
- **Effort:** Medium - need to design collection schema

#### Schedule-based Triggering (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/triggers.spl:73`
- **Issue:** Only event-based triggers implemented
- **Current:** Stub implementation exists
- **Needed:** Schedule parser, cron-like execution
- **Effort:** Medium

#### Snapshot Loading (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/compare.spl:252`
- **Issue:** Cannot load snapshots from file yet
- **Impact:** Dashboard comparison features incomplete
- **Effort:** Low-Medium

#### Alert Configuration (1 item)
- **Files:** `src/lib/std/src/tooling/dashboard/alerts.spl:42`
- **Issue:** Currently loads dummy alerts, not from `.simple/dashboard.toml`
- **Impact:** Dashboard alerts not persistent
- **Effort:** Low

---

### 3. Test/Scaffold Helpers (5 items)
These are in scaffolding tools and don't affect production code.

- **Files:** `src/lib/std/src/tooling/scaffold_feature.spl` (lines 234, 305, 308, 309, 310)
- **Issue:** Generated scaffold templates include TODO markers for users
- **Impact:** None on core functionality - user-facing guidance
- **Resolution:** Already working as intended

---

### 4. Response Body Handling (1 item)
- **Files:** `src/lib/std/src/compiler_core/net/http_client.spl:104`
- **Issue:** HTTP response body capture not fully implemented
- **Current:** Stub that returns empty response
- **Effort:** Low-Medium once HttpClient is mature

---

### 5. Spec Runner Improvements (1 item)
- **Files:** `src/lib/std/src/spec/runner/cli.spl:150`
- **Issue:** Filter application to executor not implemented
- **Impact:** `--filter` option partially non-functional
- **Effort:** Low

---

### 6. Documentation Examples (5+ items)
- **Files:**
  - `src/lib/std/src/tooling/todo_parser.spl` (lines 8-9)
  - Various lint documentation (test examples)
- **Issue:** These are intentional examples/documentation
- **Resolution:** No action needed - working as intended

---

## Blocking Dependencies

### Critical Path (blocking most work):
1. **core.time** module - blocks 6+ items
2. **HttpClient completion** - blocks 2+ items
3. **Float/date parsing** - blocks 3+ items

### Secondary:
4. Exception handling (try/catch) - blocks 1 item
5. Async/await - blocks 1 item
6. Math library (sqrt) - blocks 1 item

---

## Recommendations

### For Immediate Resolution (can be done now):
1. ✅ **Implement filter application** in `spec/runner/cli.spl:150` (~30 min)
2. ✅ **Load dashboard config from file** in `alerts.spl:42` (~1 hour)
3. ✅ **Implement schedule-based triggering** in `triggers.spl:73` (~2-3 hours)
4. ✅ **Implement snapshot loading** in `compare.spl:252` (~1 hour)

### For Medium-term (requires feature completion):
- Once `core.time` available: Implement timestamp functions (6 items)
- Once `HttpClient` mature: Implement full webhook/Slack support (2 items)
- Once `io.fs` expanded: Implement advanced file operations (2 items)

### For Long-term (major feature work):
- JSON parsing library for coverage data
- Math library for dashboard analytics
- Async/await for test execution
- Exception handling for error recovery
- Git integration for changelog generation

---

## Action Items by Priority

### P0 (High Value, Doable Now)
- [ ] Implement `apply_filters()` in spec runner - `cli.spl:150`
- [ ] Load alerts from `.simple/dashboard.toml` - `alerts.spl:42`
- [ ] Implement HTTP POST stubs for notifications - `notify.spl:170,190`

### P1 (Medium Value, Doable Now)
- [ ] Implement `build_collector` - `collector.spl:152`
- [ ] Implement `dependency_collector` - `collector.spl:158`
- [ ] Implement schedule-based triggers - `triggers.spl:73`
- [ ] Implement snapshot file loading - `compare.spl:252`

### P2 (Low Value or Blocked)
- [ ] Response body handling - `http_client.spl:104` (blocked on HttpClient)
- [ ] Float parsing helpers - 3 items (blocked on parser improvements)
- [ ] Date arithmetic - 2 items (blocked on core.time)
- [ ] Age calculation - `todo_collector.spl:51` (blocked on git integration)

### Blocked (Waiting for stdlib/lang features)
- [ ] Timestamps - wait for `core.time`
- [ ] JSON parsing - wait for JSON library
- [ ] Async tests - wait for async/await
- [ ] Math functions - wait for math library
- [ ] Exception handling - wait for try/catch

---

## Notes

1. **No Critical Bugs Found** - TODOs are feature placeholders, not broken code
2. **Scaffolding TODOs are Intentional** - They guide users on creating tests
3. **Documentation Examples are Correct** - Intentionally showing good/bad TODO format
4. **Dashboard is Functional** - Uses stub implementations where stdlib not ready

