---
name: verify
description: Production readiness verification. Checks SSpec tests for stubs/dummies, implementation completeness, requirement coverage, NFR targets, and architecture/design doc freshness. Self-sufficient — any LLM can run independently.
---

# Verify — Production Readiness Codex

**Self-sufficient.** Any LLM can run verify independently.

## Usage

- No args: verify current changes
- File path: verify specific feature
- `--all`: full project verification

## Checks

### 1. SSpec Tests
- Every `it` block has real assertions (not `pass_todo`, not `expect(true).to_equal(true)`)
- Edge cases and error paths tested
- Every REQ-NNN has test coverage

### 2. Implementation
- No stub functions (`pass_todo`, `pass_do_nothing`, `pass_dn`)
- No hardcoded returns without logic
- Error handling complete, no commented-out code

### 3. Feature Requirements
- Every REQ-NNN traced to source code
- Every BDD scenario has matching `it` block

### 4. NFR
- Performance benchmarks exist
- Security: input validation, no secrets
- Reliability: error handling paths
- Core/MCP regression gate for compiler/core/lib or MCP/LSP changes:
  - `sh scripts/check-core-runtime-smoke.shs <runtime>`
  - `SIMPLE_BINARY=<runtime> sh scripts/check-mcp-native-smoke.shs`
  - If npm packaging/release flow changed: `sh scripts/check-mcp-package-smoke.shs`

### 5. Architecture & Design Docs
- `doc/04_architecture/` updated for new modules
- `doc/05_design/` updated for new features
- Cross-references intact

## Report Format

```
[PASS] file:line — description
[FAIL] file:line — reason
[WARN] file:line — concern
```

## Pass Criteria

- Zero FAIL items
- WARN items reviewed
- STATUS: PASS before release
- Do not mark PASS for compiler/core/lib or MCP/LSP work unless the matching smoke checks passed
