# Verify Skill — Production Readiness Codex

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run verify independently. Does not depend on any other LLM having participated in prior steps.

Comprehensive verification that implementation is production-level, not dummy/stub code.

## Usage

```
/verify                          # Verify current changes (jj diff)
/verify path/to/feature_spec.spl # Verify specific feature
/verify --all                    # Full project verification
```

Argument: `$ARGUMENTS`

---

## Procedure

### Phase 1 — Scope Detection

1. If argument is a file path → verify that file and related code
2. If argument is `--all` → verify all recent features (check `jj log -n 20`)
3. If no argument → verify files in current change (`jj diff --name-only`)

Identify:
- **Spec files** (`*_spec.spl`) in scope
- **Source files** (`.spl`) changed or referenced
- **Doc files** in `doc/02_requirements/feature/`, `doc/02_requirements/nfr/`, `doc/05_design/`, `doc/04_architecture/`

### Phase 2 — SPipe System Test Verification

For each `*_spec.spl` in scope:

1. **Read every `it` block** — check that the body contains real assertions, not:
   - `pass_todo` / `pass_do_nothing` / `pass_dn` (stub markers)
   - Empty bodies or placeholder comments
   - Only `print` statements without `expect` matchers
   - Trivial `expect(true).to_equal(true)` that tests nothing
2. **Check assertion quality:**
   - Each `it` block must have at least one `expect(...).to_*()` call
   - Assertions must test actual computed values, not hardcoded constants
   - Edge cases and error paths must be tested, not just happy path
   - Placeholder helpers must fail explicitly with `assert(false)` or
     `fail(...)`, never silently pass or no-op
   - Shared interface/manual helper names must match design, spec, manual, and
     tooling references
   - Mirrored `doc/06_spec/.../*_spec.md` output for scenario-oriented specs
     must read as a manual: primary steps visible, setup expanded through
     `@prev`/`@inline`, executable SPipe folded by default, and edge/matrix
     detail folded or skipped by policy
3. **Check test coverage of requirements:**
   - Read the docstring header — extract `**Requirements:**` link
   - Read the requirement doc → list all REQ-NNN statements
   - Verify each REQ-NNN has at least one `it` block covering it
   - Flag uncovered requirements

**Report format:**
```
[PASS] spec.spl:42 — it "handles empty input" — real assertion
[FAIL] spec.spl:58 — it "processes batch" — STUB (pass_todo)
[FAIL] spec.spl:73 — it "validates auth" — DUMMY (expect(true).to_equal(true))
[WARN] REQ-005 "system shall reject expired tokens" — no test coverage
```

### Phase 3 — Implementation Verification

For each source file in scope:

1. **Detect stub/dummy implementations:**
   - Functions containing only `pass_todo`, `pass_do_nothing`, `pass_dn`
   - Functions that return hardcoded values without logic
   - Functions with `# TODO` or `# FIXME` as the only body
   - Empty method bodies in classes
2. **Check logic completeness:**
   - Error handling: `Result<T, E>` return types must handle both Ok and Err paths
   - Match statements: must cover all variants (no catch-all `_` hiding missing cases)
   - Input validation at system boundaries (user input, external APIs)
   - No commented-out code blocks left as "implementation"
3. **Production-level quality checks:**
   - No `print` used for debugging (should use proper logging)
   - No hardcoded test data in production code paths
   - No infinite loops without exit conditions
   - Resource cleanup (file handles, connections)

**Report format:**
```
[PASS] module.spl:fn process() — fully implemented
[FAIL] module.spl:fn validate() — STUB (pass_todo on line 45)
[FAIL] module.spl:fn connect() — DUMMY (returns hardcoded "ok")
[WARN] module.spl:fn parse() — TODO comment without implementation (line 92)
```

### Phase 4 — Feature Requirement Verification

1. **Find requirement doc:** `doc/02_requirements/<domain>/<topic>/<feature>.md`
   - Extract all REQ-NNN statements
   - For each REQ: trace to source code implementing it
   - Verify implementation matches the "shall" statement
   - Flag requirements with no corresponding implementation

2. **Find feature spec:** `doc/02_requirements/<domain>/<topic>/<feature>.md`
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
4. For GUI/web/2D RenderDoc+Vulkan evidence, start from the macOS top-level
   workflow:
   `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc`
   on a Mac host. Defer Windows and Linux claims until separate platform
   runbooks exist. Require host Vulkan readiness, Simple Vulkan/Engine2D readback or
   RenderDoc proof, original Chrome RenderDoc proof, Electron RenderDoc proof,
   and production GUI/web parity evidence. If Chrome or Electron logs show
   `angle=vulkan` unavailable, report
   `vulkan-angle-unavailable` and fail the Vulkan proof even when pixels render.
5. Metal/Vulkan/8K claims require matching evidence: native Metal raw readback
   on macOS, `metal-requires-macos` for Linux Metal, the Vulkan gate above for
   Vulkan, and a retained 8K row or explicit blocker in `doc/09_report` /
   `doc/10_metrics` for 8K performance.
6. For GUI/web queue proof, reject runtime-only evidence. Runtime queue/drain
   receipts are necessary but not sufficient; production proof requires
   same-frame backend `device_readback`, a positive backend handle, and matching
   checksum. Synthetic handles, upload-only provenance, and CPU mirrors fail.

### Phase 6 — Architecture & Design Doc Verification

1. **Architecture doc** (`doc/04_architecture/`):
   - If new modules/layers were added → verify `doc/04_architecture/infra/architecture_docs/overview/overview.md` or relevant arch doc is updated
   - If compiler pipeline changed → verify pipeline docs reflect the change
   - If new ADR-worthy decision was made → check `doc/04_architecture/adr/` has a record
   - Check `doc/04_architecture/compiler/misc/file_class_structure.md` references new files

2. **Design doc** (`doc/05_design/`):
   - If a new feature was implemented → verify `doc/05_design/<domain>/<topic>/<feature>.md` exists
   - Design doc must describe: data structures, algorithms, module interactions, error handling strategy
   - Design doc must cross-reference: requirements, feature spec, test files

3. **Report:**
```
[PASS] doc/05_design/batch_processing.md — exists, cross-references REQ doc
[FAIL] doc/05_design/new_parser.md — MISSING (new parser module has no design doc)
[WARN] doc/04_architecture/infra/architecture_docs/overview/overview.md — not updated for new module "optimizer_v2"
```

4. **Process documentation freshness:**
   - Workflow, tool-contract, evidence-wrapper, or verification-contract changes
     must update the matching `doc/07_guide`, `doc/06_spec`, `.codex/skills/`,
     `.agents/skills/`, `.claude/skills/`, and `.claude/agents/spipe/`
     process docs before final verification

5. **Runtime facade boundary:**
   - Run `sh scripts/audit/direct-env-runtime-guard.shs --working` and
     `sh scripts/audit/direct-env-runtime-guard.shs --staged`
   - App leaf and `src/lib/gc_async_mut` env reads or process calls outside
     owner modules must use env/process facades, not local `rt_env_get`,
     `rt_process_run`, `rt_process_run_timeout`, `rt_process_spawn_async`,
     `rt_process_wait`, `rt_process_is_running`, `rt_process_is_alive`, or
     `rt_process_kill`

---

## Final Summary

After all phases, produce a summary table:

```
== VERIFY SUMMARY ==

Phase                    | Pass | Fail | Warn |
-------------------------|------|------|------|
SPipe Tests              |   12 |    2 |    1 |
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
- If workflow/tooling changes left stale `doc/07_guide`, `doc/06_spec`,
  `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, or
  `.claude/agents/spipe/` instructions behind, do not mark verification PASS
- Do not mark PASS for scenario-oriented specs whose mirrored `doc/06_spec`
  output reads like raw test mechanics instead of an operator/user manual
- Do not mark PASS if `direct-env-runtime-guard.shs --working` or `--staged`
  fails
- Read actual source code — do not trust file names or comments alone
- Fail wrapper verification if a production MCP or LSP launcher executes raw source instead of a cached compiled artifact
- Audit request handlers for repeated scans, repeated rereads, and per-request subprocesses in hot paths
- Verify cache invalidation exists for writes that affect cached or indexed data
- Require startup and representative request perf evidence for performance-sensitive tooling changes

### Security fail-closed regression checks (web / AOP / capability)

Treat any of these as **FAIL** when reviewing web-app / AOP / capability changes:

- **Fail-open advice/auth**: security advice or auth/deny handlers that return
  `void` (or `()`), so the weaver's `is_err()` denial gate can never fire. Security
  advice must return `Result<(), text>`.
- **Forgeable CSRF**: CSRF validating or minting tokens under an empty `secret_key`
  (must deny). Token compare must use `std.common.crypto.constant_time_compare`,
  not `==` and not a per-module copy.
- **CORS cache leak / reflection bypass**: reflecting a concrete Origin without
  `Vary: Origin`, or `*` + `Allow-Credentials: true`, or accepting `null` Origin.
- **Header injection**: response header values not checked for CRLF.
- **Rate-limit XFF spoof**: keying on `X-Forwarded-For` without a `trusted_proxies`
  gate (must default to direct `peer_addr`).
- **Capability fail-open**: parsers/lookups returning a wildcard/`full()` grant on
  malformed/unknown input, or uninitialized subjects defaulting to all-rights.
- **Weak crypto randomness**: tokens/session-IDs/salts/keys drawn from the LCG
  (`std.random` / `random_pure` / `rt_random_next`) instead of the CSPRNG
  (`random_hex`/`random_bytes` → `rt_random_hex`, OsRng/`/dev/urandom`).
- Confirm a header-setting phase result can actually emit headers (not stuff them
  into the response **body**) before crediting a header-based control as effective.

### Crash-containment regression checks (threads / async / actors / AOP / channels)

Treat any of these as **FAIL** when reviewing runtime/concurrency/AOP changes
(contract established 2026-06-11, guide: `doc/07_guide/runtime/crash_debugging.md`):

- **Bare panic boundary**: task/actor/advice execution sites calling user code
  without `catch_unwind` (Rust) or without recording a death reason — one task's
  failure must never kill sibling tasks, the worker, or the process.
- **Swallowed failure**: `let _ = handle.join()`, `Err(_) => return 0/NIL`, or
  discarded `DispatchResult` with no recorded reason. Every catch must leave a
  queryable record (`rt_actor_death_reason`, `take_last_task_panic`,
  `last_death_reason`, `aop_last_denial`, `rt_aop_last_error`).
- **Poisonable global lock**: `.lock().unwrap()` on a global registry mutex
  (use `.unwrap_or_else(|e| e.into_inner())` — one panic must not cascade).
- **Silent drop channel APIs**: new send/recv paths that silently drop on
  closed/full instead of signaling (`try_send`/closed-flag pattern); parked
  waiters that nothing can ever wake (close must drain).
- **NIL-as-error leak**: returning `RuntimeValue::NIL` (bit pattern prints as 3)
  for invalid input on a value-returning extern — either be the identity
  (already-resolved semantics) or record + report the error.
- **Unconditional diagnostic overhead**: new per-call tracing/backtrace capture
  not gated behind a `SIMPLE_*` env flag (presence = on, default OFF). Always-on
  recording is acceptable only on failure paths.
- **Fix without pin**: any bug fix shipped without a regression spec that fails
  on the pre-fix behavior (no skip(), no weakened asserts, verified green via
  `bin/simple test`/`run`).
- **Lean drift**: changes to weaver/scheduler/channel/boundary semantics without
  rechecking the matching `src/verification/*` model
  (`scripts/check/check-lean-proofs.shs` must stay green, zero sorry).
