---
name: verify
description: "Codex verification skill (primary verifier in cooperative mode). 6-phase production readiness verification: scope, SSpec quality, implementation stubs, requirements tracing, NFR, docs. STATUS: PASS/FAIL/WARN output. Must PASS before release."
---

# Verify — Codex (Primary Verifier)

**Cooperative Phase:** Verification (final gate before release)
**Self-sufficient.** Any LLM can run verify independently. Codex is the primary verifier in cooperative mode.

## Tools

- **Simple MCP** — query codebase structure, find stubs
- **Simple LSP MCP** — symbol lookup, dead code detection

## Usage

- No args: verify current changes
- File path: verify specific feature
- `--all`: full project verification

## 6-Phase Verification

### Phase 1: Scope Analysis

- Identify all files changed/added for the feature
- Map changes to requirements (REQ-NNN)
- Verify no unrelated changes sneaked in

### Phase 2: SSpec Quality

- Every `it` block has real assertions (not `pass_todo`, not `expect(true).to_equal(true)`)
- Edge cases and error paths tested
- Every REQ-NNN has at least one test
- Built-in matchers only: `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`

### Phase 3: Implementation Stubs

Scan for stub patterns — any match is a **FAIL**:

- `pass_todo` — unimplemented placeholder
- `pass_do_nothing` / `pass_dn` without documentation — unjustified no-op
- Hardcoded returns without logic
- Empty function bodies
- Commented-out code blocks
- `# TODO` / `# FIXME` converted to `# NOTE` — hidden work

**STUB001 = HARD FAIL.** No stubs in production code.

### Phase 4: Requirements Tracing

- Every REQ-NNN in `doc/02_requirements/feature/<feature>.md` traced to source code
- Every BDD scenario in `doc/06_spec/` has matching `it` block in test files
- No orphan requirements (REQ without implementation)
- No orphan tests (tests without corresponding REQ)

### Phase 5: NFR Verification

- **Performance:** benchmarks exist for performance-critical paths
- **Security:** input validation present, no hardcoded secrets
- **Reliability:** error handling complete, `Result<T, E>` + `?` used consistently
- **Maintainability:** files under 800 lines, no duplication

### Phase 6: Documentation Freshness

- `doc/04_architecture/` updated for new modules
- `doc/05_design/` updated for new features
- Cross-references between docs intact
- CHANGELOG updated for user-facing changes

## Report Format

```
=== Verification Report: <feature> ===

[PASS] src/lib/feature.spl:42 — REQ-001 implemented with error handling
[PASS] test/lib/feature_spec.spl:15 — REQ-001 has 3 test cases
[FAIL] src/lib/feature.spl:87 — pass_todo found (STUB001)
[FAIL] test/lib/feature_spec.spl:30 — expect(true).to_equal(true) is not a real assertion
[WARN] doc/04_architecture/feature.md — not updated for new module

STATUS: FAIL (2 failures, 1 warning)
```

## Pass Criteria

- **Zero FAIL items** — any FAIL blocks release
- **WARN items reviewed** — warnings must be acknowledged
- **STATUS: PASS** required before release

## Artifacts Produced

| Artifact | Path |
|----------|------|
| Verification report | Printed to stdout / saved to `doc/09_report/verify_<feature>.md` |

## Rules

- NEVER downgrade a FAIL to WARN — fix the issue
- NEVER skip stub detection — STUB001 is non-negotiable
- NEVER mark STATUS: PASS with outstanding FAILs
- If verification finds issues, report them — do not auto-fix without user approval
- Fail production wrapper verification if an MCP or LSP launcher executes a source entrypoint directly instead of a cached compiled artifact
- Audit hot request paths for repeated full scans, repeated file rereads, and per-request subprocesses; flag uncached patterns as FAIL or WARN based on impact
- Verify cache invalidation exists for write flows that affect cached or indexed data
- Require startup and representative request performance evidence for performance-sensitive tooling changes
