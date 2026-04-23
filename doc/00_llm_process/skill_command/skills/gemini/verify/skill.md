# verify

Source: `.gemini/commands/verify.toml`

## Description

Production readiness verification. Checks tests, implementation, requirements, NFR, and docs.

## Prompt

Run production readiness verification. Self-sufficient — any LLM can run independently.

Check scope: current changes (default), specific file, or --all for full project.

Phase 1: Scope Detection — identify spec files, source files, doc files in scope.

Phase 2: SSpec Tests — every it block has real assertions (not pass_todo, not expect(true).to_equal(true)).

Phase 3: Implementation — no stub functions, no hardcoded returns, complete error handling.

Phase 4: Feature Requirements — every REQ-NNN traced to code + test.

Phase 5: NFR — performance benchmarks, security, reliability, observability.

Phase 6: Architecture & Design Docs — doc/04_architecture/ and doc/05_design/ updated.

Report: [PASS], [FAIL], [WARN] per item, summary table at end.
Must show STATUS: PASS before release.
Fail wrapper verification if a production MCP or LSP launcher executes raw source instead of a cached compiled artifact.
Audit hot request paths for repeated scans, repeated rereads, per-request subprocesses, and missing cache invalidation on writes.
Require startup and representative request perf evidence for performance-sensitive tooling changes.
