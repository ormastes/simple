# Verify Skill — Production Readiness (MCP Plugin)

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run verify independently via MCP tools. Does not depend on any other LLM having participated in prior steps.

Comprehensive verification that implementation is production-level, not dummy/stub code.

## Usage

```
/verify                          # Verify current changes
/verify path/to/feature_spec.spl # Verify specific feature
/verify --all                    # Full project verification
```

Argument: `$ARGUMENTS`

---

## MCP Tools Used

This skill uses the `simple-mcp` server tools for automated checks:

| MCP Tool | Purpose |
|----------|---------|
| `simple_test` | Run SSpec tests |
| `simple_lint` | Run linter checks |
| `simple_check` | Run all build checks |
| `simple_check_arch` | Verify architecture constraints |
| `simple_diagnostics` | Get compiler diagnostics |
| `simple_search` | Search source code for patterns |
| `simple_read` | Read file contents |
| `simple_diff` | View changes |
| `simple_status` | View project status |
| `simple_stats` | Get project statistics |
| `simple_doc_coverage` | Check documentation coverage |
| `simple_spec_coverage` | Check spec coverage |
| `simple_todo_scan` | Scan for TODO/FIXME markers |
| `simple_verify` | Run built-in verification |

---

## Procedure

### Phase 1 — Scope Detection

1. Use `simple_status` to see current project state
2. Use `simple_diff` to identify changed files
3. If argument is a file path, focus on that file and related code
4. If argument is `--all`, verify all recent features

Identify:
- **Spec files** (`*_spec.spl`) in scope
- **Source files** (`.spl`) changed or referenced
- **Doc files** in `doc/02_requirements/feature/`, `doc/02_requirements/nfr/`, `doc/05_design/`, `doc/04_architecture/`

### Phase 2 — SSpec System Test Verification

For each `*_spec.spl` in scope:

1. Use `simple_read` to read every `it` block — check that the body contains real assertions, not:
   - `pass_todo` / `pass_do_nothing` / `pass_dn` (stub markers)
   - Empty bodies or placeholder comments
   - Only `print` statements without `expect` matchers
   - Trivial `expect(true).to_equal(true)` that tests nothing
2. **Check assertion quality:**
   - Each `it` block must have at least one `expect(...).to_*()` call
   - Assertions must test actual computed values, not hardcoded constants
   - Edge cases and error paths must be tested, not just happy path
3. **Check test coverage of requirements:**
   - Read the docstring header — extract `**Requirements:**` link
   - Read the requirement doc, list all REQ-NNN statements
   - Verify each REQ-NNN has at least one `it` block covering it
   - Flag uncovered requirements
4. Use `simple_test` to run the spec and confirm it passes
5. Use `simple_spec_coverage` to check overall spec coverage

**Report format:**
```
[PASS] spec.spl:42 — it "handles empty input" — real assertion
[FAIL] spec.spl:58 — it "processes batch" — STUB (pass_todo)
[FAIL] spec.spl:73 — it "validates auth" — DUMMY (expect(true).to_equal(true))
[WARN] REQ-005 "system shall reject expired tokens" — no test coverage
```

### Phase 3 — Implementation Verification

For each source file in scope:

1. **Detect stub/dummy implementations** using `simple_search`:
   - Functions containing only `pass_todo`, `pass_do_nothing`, `pass_dn`
   - Functions that return hardcoded values without logic
   - Functions with `# TODO` or `# FIXME` as the only body
   - Empty method bodies in classes
2. **Check logic completeness:**
   - Error handling: `Result<T, E>` return types must handle both Ok and Err paths
   - Match statements: must cover all variants (no catch-all `_` hiding missing cases)
   - Input validation at system boundaries (user input, external APIs)
   - No commented-out code blocks left as "implementation"
3. **Production-level quality checks** using `simple_lint`:
   - No `print` used for debugging (should use proper logging)
   - No hardcoded test data in production code paths
   - No infinite loops without exit conditions
   - Resource cleanup (file handles, connections)
4. Use `simple_todo_scan` to find remaining TODOs/FIXMEs

**Report format:**
```
[PASS] module.spl:fn process() — fully implemented
[FAIL] module.spl:fn validate() — STUB (pass_todo on line 45)
[FAIL] module.spl:fn connect() — DUMMY (returns hardcoded "ok")
[WARN] module.spl:fn parse() — TODO comment without implementation (line 92)
```

### Phase 4 — Feature Requirement Verification

1. **Find requirement doc:** `doc/02_requirements/feature/<feature>.md`
   - Extract all REQ-NNN statements
   - For each REQ: trace to source code implementing it
   - Verify implementation matches the "shall" statement
   - Flag requirements with no corresponding implementation

2. **Find feature spec:** `doc/02_requirements/feature/<feature>.md`
   - Extract all BDD scenarios (Given/When/Then)
   - Verify each scenario has a corresponding `it` block in `*_spec.spl`
   - Verify acceptance criteria checkboxes

3. **Report:**
```
[PASS] REQ-001 "system shall parse SDN files" — implemented in parser.spl:fn parse_sdn()
[FAIL] REQ-003 "system shall validate schemas" — NO IMPLEMENTATION FOUND
[WARN] Feature scenario "error on malformed input" — no matching test
```

### Phase 5 — NFR Verification

1. **Find NFR doc:** `doc/02_requirements/nfr/<feature>.md`
2. For each NFR category present:
   - **Performance:** Check if benchmarks or timing tests exist
   - **Reliability:** Check error handling paths, graceful degradation
   - **Security:** Check input validation, no secrets in code, proper auth
   - **Observability:** Check logging, metrics, tracing
   - **Compatibility:** Check platform-specific code paths
3. Flag NFR targets with no verification mechanism

### Phase 6 — Architecture & Design Doc Verification

1. **Architecture doc** (`doc/04_architecture/`):
   - Use `simple_check_arch` to verify architecture constraints
   - If new modules/layers were added, verify arch docs are updated
   - If compiler pipeline changed, verify pipeline docs reflect the change
   - If new ADR-worthy decision was made, check `doc/04_architecture/adr/` has a record

2. **Design doc** (`doc/05_design/`):
   - If a new feature was implemented, verify design doc exists
   - Design doc must describe: data structures, algorithms, module interactions, error handling strategy
   - Design doc must cross-reference: requirements, feature spec, test files
   - Use `simple_doc_coverage` to check documentation coverage

3. **Report:**
```
[PASS] doc/05_design/batch_processing.md — exists, cross-references REQ doc
[FAIL] doc/05_design/new_parser.md — MISSING (new parser module has no design doc)
[WARN] doc/04_architecture/overview.md — not updated for new module "optimizer_v2"
```

---

## Final Summary

After all phases, produce a summary table:

```
== VERIFY SUMMARY ==

Phase                    | Pass | Fail | Warn |
-------------------------|------|------|------|
SSpec Tests              |   12 |    2 |    1 |
Implementation           |   28 |    1 |    3 |
Feature Requirements     |    8 |    1 |    0 |
NFR                      |    4 |    0 |    2 |
Architecture & Design    |    3 |    1 |    1 |
-------------------------|------|------|------|
TOTAL                    |   55 |    5 |    7 |

STATUS: FAIL (5 failures must be fixed before release)
```

- **FAIL** items must be fixed — they indicate missing or dummy implementations
- **WARN** items should be reviewed — they may be acceptable with justification
- **PASS** means production-ready

---

## Rules

- NEVER mark a stub (`pass_todo`) as PASS
- NEVER accept `expect(true).to_equal(true)` as real test coverage
- NEVER skip NFR checks — even if no NFR doc exists, note it as WARN
- If no requirement doc exists for a feature, flag as WARN (not FAIL)
- If design doc exists but is outdated (references deleted files/functions), flag as FAIL
- Read actual source code — do not trust file names or comments alone
- Fail wrapper verification if a production MCP or LSP launcher executes raw source instead of a cached compiled artifact
- Audit request handlers for repeated scans, repeated rereads, and per-request subprocesses in hot paths
- Verify cache invalidation exists for writes that affect cached or indexed data
- Require startup and representative request perf evidence for performance-sensitive tooling changes
