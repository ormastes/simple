---
name: impl
description: Implement a feature end-to-end. Self-sufficient — if research, requirements, or design are missing, creates them first. Covers implementation, testing, duplication check, refactoring, and verification.
---

# Impl — Self-Sufficient 15-Phase Workflow

**Self-sufficient.** If research, requirements, or design missing, does them first (phases 1-5).

## Prerequisites Check

| Artifact | Path | If exists, skip to |
|----------|------|--------------------|
| Research | `doc/01_research/local/<feature>.md` | Phase 4 |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Phase 4 |
| Architecture | `doc/04_architecture/<feature>.md` | Phase 6 |
| Design | `doc/05_design/<feature>.md` | Phase 6 |
| System tests | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` | Phase 8 |
| Generated spec docs | `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md` | Phase 8 |

**If ALL exist**, skip to Phase 8 (Implementation).

## Phases

1-3: Research + Requirements (skip if exist, otherwise do inline)
4-5: Plan + Design + Architecture (skip if exist)
6-7: System Test + Doc Consistency
8: Implementation in `src/**/<feature>.spl`
9-10: Unit + IT Tests (80%+ coverage) + Doctest
11-13: Bug Reports + Duplication Check + Refactoring
14: Full Test Suite (`bin/simple test && bin/simple build lint`)
15: Run $verify + final smoke checks + VCS Sync

## Rules

- **One App, One Host Interface:** Implement apps for all OSes identically; platform difference lives only in HAL backends (SOSIX, CompositorBackend, DedicatedHost), config, or optional capabilities. Never add per-OS app files, platform conditionals in app code, or duplicated adapters. See `doc/04_architecture/os/one_app_host_interface_rule.md`.
- Standalone target products such as Office are not compiler bootstrap: consume
  an explicitly admitted Phase 3 compiler, write cache/output outside
  `build/bootstrap`, and fail closed if its receipt is absent. Never use the
  Rust seed as a product-build fallback; Phase 3 remains unsuitable for deploy,
  SPipe execution, or release evidence.

- All code in `.spl` — no Python, no Bash
- Stub Prevention: no `pass_todo` in final code, STUB001 = hard fail
- 80%+ branch coverage target
- For scenario-oriented specs, run the generated-manual review loop before
  claiming completion:
  `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`, read the
  output like a manual, then revise steps/captures/visibility until primary
  flows are manual-quality, noisy details are folded or skipped, and the
  generator reports `0 stubs`.
- Run `simple sspec-maintain scan <spec>` for each changed SSpec/manual pair.
  Review all seven scores and stable findings; blockers, missing/stale mirrors,
  policy regression, machine-output contamination, or fail-fast scaffold
  placeholders prevent completion.
  `improve` is preview-only until an exact patch is confirmed and rollback is
  retained. `documentize` reuses SPipe; optional LLM advice never affects the
  deterministic score or self-applies. `scaffold` preserves source
  path/hash/line and REQ identity, emits no inferred passing oracle, and remains
  fail-fast until implemented. The planned external-standard command is
  `spec-to-spipe`; future `spec-to-sspec` compatibility must delegate to it.
  Neither is a production CLI yet.
- If design introduced shared interface or manual setup/checker helper
  placeholders, implement them or keep them failing explicitly with
  `assert(false)` or `fail(...)`. Silent no-op helpers are not valid coverage.
- For broad lanes, preserve the cooperative review plan from design: lower-model
  sidecars such as Codex Spark, Claude Haiku, or Claude Sonnet must be merged or
  explicitly `N/A`, then a normal/highest-capability reviewer must accept broad
  findings, generated-manual quality, coverage claims, exclusions, and done
  marks before implementation handoff.
- When implementation changes workflow/tooling, evidence wrappers, generated
  specs, or verification contracts, update the matching `doc/07_guide`,
  `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, and `.gemini/commands/` instructions before `$verify`; stale process docs are
  implementation work, not release cleanup.
- For `simple_context` or context-mode changes, keep the MCP/tooling guide and
  mirrored generated manuals current. SQL-backed context paths must document the
  `--sql`/`--db` CLI flags, embedded SQLite facade boundary, explicit absence
  statuses, and public-absence guard.
- Executable specs must stay under `test/`; generated/manual docs mirror that
  path under `doc/06_spec` after stripping the leading `test/` segment and must
  be `.md` only. Require
  `find doc/06_spec -name '*_spec.spl' | wc -l` to print `0` before sync.
- For `simple run` script-startup work, preserve the driver fast path for `.shs`,
  `get_cli_args`, and `std.cli` scripts; verify
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` before claiming
  completion.
- Files > 800 lines must be split
- Run $verify before VCS sync
- For compiled feature work, follow
  `doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md`: build
  the smallest named target/provider/SCI projection, retain its compatibility
  receipt, and never infer full bootstrap from a compiler path.
- If compatibility evidence selects full bootstrap, use the canonical
  `bootstrap-from-scratch.sh --strategy=normal|full` scheduler path and require
  its unchanged generation lease plus qualified lineage receipt. A
  `failure-manifest.env` or any recursive invalidation forbids descendant
  deployment. See `doc/07_guide/tooling/bootstrap_speculative_scheduler.md`.
- Focused compiler/interpreter/loader work may use an admitted Stage 2 or 3
  binary per that guide. Record path/hash/stage/provenance/commands, isolate
  output/cache, fail closed, and label evidence by stage; never promote it to
  Stage 4, general SPipe/docgen/test, release, convergence, or cross-host proof.
- If `src/compiler/**`, `src/lib/**`, `src/app/mcp/**`, `src/app/simple_lsp_mcp/**`, or MCP packaging files changed, finish with:
  - `<runtime> check src/compiler`
  - `<runtime> check src/lib`
  - `<runtime> check src/app/mcp`
  - `<runtime> check src/app/simple_lsp_mcp`
  - `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  - If publish/package flow changed:
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`

## Compiler/backend stage split

Keep the legacy pipeline canonical until one admitted end-to-end receipt.
Afterward use Stage 1 Rust seed, the unchanged existing canonical pure-Simple
builds for admitted Stage 2 and Stage 3, and Stage 4
tools-only linking exact versioned Stage-3 archives/interfaces. Stage 4 records
zero `src/compiler/**` units and rejects source, interface, archive, runtime-
ABI, producer, or receipt mismatch before tool compilation. Acceptance needs a
real runner, independent sabotage, exact-fresh-CLI essential tools, and audit-
full behavior equivalence. Static checks and Rust fallback are not acceptance.
Label bounded Rust-seed execution diagnostic-only. Tool acceptance resolves the
exact admitted Stage-3 compiler identity, builds and executes the tool,
validates `ToolingLinkReceiptV1`, and rejects Rust-seed, fake, or stale compiler
identities.
Runtime authority is complete only when an exact required-symbol manifest is
hash-bound to the admitted archive and Stage-3 identity. A missing symbol,
hosted provider, generated stub, or fallback marker fails before link. Run the
built tool's bounded `--help`/`--version` only after link success and validated
`ToolingLinkReceiptV1`.

## Implementation Language Policy

Pure Simple first — never implement in C what pure Simple can do; bootstrap C
keeps a pure-Simple twin (`scripts/check/check-dual-run-shadow.shs`); HAL code
minimizes asm (typed register views > optimization-restraining tags >
intrinsics > inline asm for irreplaceable ops only). Full policy:
`doc/07_guide/os/hal/pure_simple_hal.md`.
