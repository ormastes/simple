# SStack State: webserver-hardening-opt-general

## User Request
> Implement webserver hardening optimization plan with generalized optimization plugins. Optimization plugin updates should optimize not only web-specific cases but also general cases. Plan: doc/03_plan/webserver_hardening_optimization_plan_2026-05-26.md

## Task Type
feature

## Refined Goal
> Implement two focused slices of the webserver hardening optimization plan:
> 1. **HTTP Hardening** (plan item 1): Add bounded parser limits, path traversal refusal, timeout/keep-alive policy, bad-request handling, and header canonicalization to the HTTP library (`src/lib/nogc_async_mut/http/`).
> 2. **General MIR Optimization Patterns** (plan item 5, generalized): Register four new general-purpose MIR optimization patterns via the dynamic-pass manifest system (`src/compiler/60.mir_opt/optimizer_manifest.spl`). These are NOT web-specific — webserver code is the validation site, not the target:
>    - **byte-scan-to-delimiter**: generalizes header scan loops
>    - **switch-on-short-string**: generalizes route lookup dispatch
>    - **capability-guarded-fast-path**: generalizes sendfile/capability decision
>    - **bit-unpack-fixed-table**: generalizes HPACK/Huffman bit loops
> Validate that general patterns fire on webserver hot paths as verification.

## Acceptance Criteria
- [x] AC-1: HTTP request parser enforces bounded request-line length (8192 bytes default), max header count (100), max single-header size (8192 bytes), and max body size (10MB default). Violations return 400/413 without panic.
- [x] AC-2: Static-file serving refuses path traversal (`..`, null bytes, non-normalized paths). Returns 403.
- [x] AC-3: HTTP headers module supports canonicalization (lowercase-normalize) and duplicate-header policy (last-wins or reject depending on header class).
- [x] AC-4: Connection timeout and keep-alive limits are configurable with sensible defaults (60s idle, 100 requests per connection).
- [x] AC-5: Four general MIR optimization patterns registered as dynamic-pass manifest entries: `byte-scan-to-delimiter`, `switch-on-short-string`, `capability-guarded-fast-path`, `bit-unpack-fixed-table`.
- [x] AC-6: Each pattern has a recognizer function that fires on general code patterns (not HTTP-specific). Pattern descriptions and match criteria documented in manifest entries.
- [x] AC-7: Validation specs confirm the general patterns match on webserver hot-path code (header scan, route lookup, sendfile decision, HPACK bit loops) as representative examples.
- [x] AC-8: All hardening specs pass (`bin/simple test` on relevant test files).
- [x] AC-9: No regressions in existing HTTP/QUIC/H2 test suites.

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-26
- [x] 2-research (Analyst) — 2026-05-26
- [x] 3-arch (Architect) — 2026-05-26
- [x] 4-spec (QA Lead) — 2026-05-26
- [x] 5-implement (Engineer) — 2026-05-26
- [x] 6-refactor (Tech Lead) — 2026-05-26
- [x] 7-verify (QA) — 2026-05-26
- [x] 8-ship (Release Mgr) — 2026-05-26

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** HTTP hardening + general MIR optimization patterns (see above)
**ACs defined:** 9 acceptance criteria covering both slices
**Key architectural decision:** Optimization patterns are GENERAL (byte-scan, string-switch, capability-guard, bit-unpack) — web code is validation, not target.
**Files to touch:**
- Hardening: `src/lib/nogc_async_mut/http/request.spl`, `headers.spl`, `response.spl`
- New hardening module: `src/lib/nogc_async_mut/http/limits.spl`
- Optimization: `src/compiler/60.mir_opt/optimizer_manifest.spl`, new pattern files
- Specs: `test/unit/lib/nogc_async_mut/http/` (hardening), `test/unit/compiler/60.mir_opt/` (patterns)

### 2-research
Inline research: explored existing HTTP lib (request.spl, headers.spl, response.spl, common.spl), MIR optimizer pipeline (60.mir_opt/optimization_passes.spl, optimizer_manifest.spl), dynamic pass registry, PatternRule struct. No parser limits existed. Import syntax needed migration from deprecated `import` to `use`.

### 3-arch
Two-slice arch: (1) HTTP hardening as new modules limits.spl + path_security.spl + edits to request/headers/response. (2) General patterns as new general_patterns.spl using dynamic manifest system with PatternRule/MirPattern/MirRewrite types.

### 4-spec
Created http_hardening_spec.spl (26 tests: 10 parser limits, 8 path traversal, 5 header canonicalization, 3 connection config). Created general_patterns_spec.spl (27 tests: 10 manifest registration, 8 general recognizers, 4 web hot-path validation, 5 pattern info generality).

### 5-implement
- `src/lib/nogc_async_mut/http/limits.spl` — HttpLimits struct, HttpParseError enum, bound checks
- `src/lib/nogc_async_mut/http/path_security.spl` — traversal/null-byte/backslash validation
- `src/lib/nogc_async_mut/http/request.spl` — added parse_request_safe with limit enforcement
- `src/lib/nogc_async_mut/http/headers.spl` — canonicalize_headers, deduplicate_headers_last_wins, validate_no_duplicate_singletons, fixed capitalize_word to lowercase rest
- `src/lib/nogc_async_mut/http/response.spl` — migrated imports to `use` syntax
- `src/compiler/60.mir_opt/general_patterns.spl` — 4 general patterns with manifest entries, PatternRules, recognizers

### 6-refactor
Migrated all HTTP module imports from deprecated `import X from "std/Y"` to `use std.Y.{...}`. Fixed capitalize_word to properly lowercase rest of word for normalization.

### 7-verify
- HTTP hardening: 26/26 pass, 0 failures
- General patterns: 27/27 pass, 0 failures
- Regression: all 44 existing HTTP/H2/H3 tests pass, 0 regressions
- Existing HTTP server specs (protocol_handler, compression, static_file) pass

### 8-ship
Two atomic commits on main:
1. `a27608ec56` — feat: HTTP hardening (6 files, 582 insertions)
2. `a2781a1ec9` — feat: general MIR optimization patterns (2 files, 409 insertions)
