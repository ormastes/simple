# Feature: Full Pure-Simple SIMD Bootstrap

## Raw Request
$sp_dev do bootstrap redeploy mcp and simple. fuly apply avx512 and other simd. full db/web server and none platform dpends. pure simple. done than push. research and current research doc about simd and design doc. plan design and go pherallel.

## Task Type
feature

## Refined Goal
Deliver, verify, deploy, and push a pure-Simple portable SIMD implementation with runtime-selected AVX-512 and other major SIMD backends, apply it to the database and web-server hot paths without app-layer platform dependencies, and rebuild the Stage 4 Simple CLI and MCP servers from the admitted bootstrap lineage.

## Acceptance Criteria
- AC-1: Current local and domain research documents inventory the existing SIMD language/runtime/compiler surfaces, current dirty-worktree SIMD changes, database and web-server hot paths, bootstrap/deployment contracts, and authoritative prior research; every existing research document is preserved and new findings are appended or placed in the canonical `doc/01_research/{local,domain}/full_pure_simple_simd_bootstrap.md` files.
- AC-2: The user selects final functional and NFR requirements from option documents that state pros, cons, and effort; canonical `doc/02_requirements/feature/full_pure_simple_simd_bootstrap.md` and `doc/02_requirements/nfr/full_pure_simple_simd_bootstrap.md` contain numbered requirements, and the selected lane has no lingering pending-selection option files.
- AC-3: The architecture and detail design define one portable pure-Simple vector API and ProcessingIR path with runtime capability selection for scalar, x86 SSE2/SSSE3/SSE4.1/AVX/AVX2/AVX-512, Arm NEON/SVE, RISC-V V, and WebAssembly SIMD128 where the compiler target supports them; unsupported capabilities fail closed to the scalar implementation with identical public semantics.
- AC-4: App and library code for the database and web server contains no per-OS sibling implementation, target-OS branch, direct platform-runtime dependency, or duplicated adapter; platform differences remain behind the existing HAL/capability boundary, and direct environment/process guards pass.
- AC-5: Representative database scan/filter/hash/compare/encoding and web-server parse/route/header/body/encoding hot paths use the shared portable SIMD interfaces when profitable, retain bounded scalar tails and scalar fallback, and produce byte-for-byte or value-for-value equivalent results across supported lane widths, unaligned inputs, empty inputs, boundary sizes, and adversarial data.
- AC-6: AVX-512 and every implemented SIMD backend has feature detection that prevents unsupported instruction execution, documents required CPU/OS state checks, and has focused unit/integration coverage plus executable SSpec scenarios mapped to the final REQ identifiers; tests use concrete typed assertions and contain no placeholder pass, fabricated receipt, or Rust-seed substitution.
- AC-7: Performance evidence measures warm Simple/MCP startup, representative database and web-server request latency/throughput, and max RSS on realistic fixtures; it records scalar versus selected-SIMD results and treats any meaningful regression as a fix or a tracked bug with a precise resume condition.
- AC-8: Production implementation in this lane is pure Simple under `src/compiler`, `src/lib`, and `src/app`; no new Rust, C, C++, platform-specific app leaf, foreign SIMD wrapper, or raw-source production wrapper is required. Any unavoidable lower-runtime/compiler dependency must be proven as the existing correct HAL boundary and documented rather than silently expanded.
- AC-9: Design artifacts exist and agree: `doc/04_architecture/full_pure_simple_simd_bootstrap.md`, its TLDR companion, `doc/05_design/full_pure_simple_simd_bootstrap.md`, `doc/03_plan/sys_test/full_pure_simple_simd_bootstrap.md`, and `doc/03_plan/agent_tasks/full_pure_simple_simd_bootstrap.md`; the processing backend architecture/TLDR/guide remain current and database/web integration boundaries are explicit.
- AC-10: Executable SSpec is under `test/` and its mirrored `doc/06_spec` Markdown reads as an operator manual using the shared steps `step_detect_simd_capabilities`, `step_run_scalar_oracle`, `step_run_simd_backend`, `step_compare_database_results`, `step_compare_web_results`, `step_bootstrap_platform_handoff_readiness`, and `step_verify_deployed_tools`; `doc/06_spec` contains zero `*_spec.spl` files.
- AC-11: Bootstrap evidence follows the canonical Gate 1-6 order without seed, stale-artifact, cross-build, or raw-source substitution: admitted Stage 3 receipt; x86_64 Linux Stage 4; frozen candidate identity/hash; all four exact-candidate essential-tool smoke markers; deployment followed by rollback receipt; and selected native/QEMU/platform acceptance. Missing hosts remain active BLOCKED rows and no failed command is repeated beyond three distinct fix/verify cycles.
- AC-12: The exact admitted Stage 4 candidate passes `post_bootstrap_stage4_acceptance_spec.spl`, compiler/lib/MCP/LSP checks, MCP stdio integration, required core runtime and MCP native smoke checks, release-bound `bin/simple test test --whole --mode=interpreter`, full applicable lint and duplicate gates, and production-readiness verification with `STATUS: PASS` exactly once per unchanged acceptance criterion.
- AC-13: The verified Stage 4 candidate is deployed as the canonical `simple` executable and both MCP server artifacts through cached compiled production wrappers; deployment receipts bind source revision, candidate path/hash, provenance, rollback outcome, MCP startup/request/RSS evidence, and the current MCP startup-performance lane state and guide.
- AC-14: Knowledge is updated in the same change: relevant research, architecture, design, plans, generated/manual specs, database/web/SIMD/compiler/MCP guides, feature and layer expert `skill.md` files, feature tracking, and bug/Todo records for every unresolved gap. Workflow/verification files in `.codex`, `.agents`, `.claude`, and `.gemini` are updated only if their contract changes; otherwise the plan records `N/A` with a concrete reason. Must-check ledger v3 rows name owners and actionable unblock conditions, and PASS receipts use the canonical recorder.
- AC-15: Final verification audits every requirement and retained blocked platform row, accepts the cooperative reviews and generated-manual quality, commits only intentional lane-owned files, rebases linearly with `jj`, and pushes the verified source, deployment metadata, and release/tag state using the already-authorized push after all release gates pass.
- AC-16: A separate phase-verification matrix records the exact binary path, hash, provenance, supported-command set, isolated cache/output, command, exit status, and retained receipt for compiler and interpreter checks plus MCP, SPipe, DevHub, and LLM Caret suites at every bootstrap phase. Stage 2/3 rows run only receipt-admitted focused checks and remain explicitly non-release evidence; Stage 4 runs every applicable component check and its complete unit, integration, system, and release-bound test suites with no seed or stale-binary fallback. A failure blocks promotion to the next phase and is fixed or retained as an owned actionable blocker within the three-cycle cap.

- AC-17 (user refinement, 2026-09-08): At each bootstrap phase actually launch the exact admitted compiler/interpreter, MCP/LSP MCP, SPipe plugin, LLM Caret, and DevHub; execute their applicable suites and live protocol sanity. DevHub independently proves authenticated read access to GitHub, Jira, and Confluence against known fixture identities. Configuration-only auth status, help output, fixtures, static scans, and later-phase artifacts cannot earn a live PASS. Every unavailable row keeps its owner, prerequisite, retained artifacts, and exact resume command.

## Scope Exclusions
- New database query-language features, new HTTP protocol features, and unrelated application redesigns are excluded unless research proves they are required to exercise or validate the SIMD integration.
- Platform-specific SIMD assembly exposed directly to database or web-server modules is excluded; target lowering belongs below the shared portable compiler/HAL boundary.
- Unrelated dirty files and concurrent feature lanes are excluded from this lane unless their owner explicitly transfers them into the integration plan.

## Cooperative Review
- Sidecar lane `simd-current-state`: inspect current SIMD research, code, tests, target coverage, and uncommitted overlap; no edits until ownership is established.
- Sidecar lane `db-web-portability`: inspect database/web hot paths, platform dependencies, pure-Simple boundaries, and performance fixtures; no edits until ownership is established.
- Sidecar lane `bootstrap-deploy`: inspect Stage 3/4 receipts, Simple/MCP deployment wrappers, smoke gates, and active blockers; no edits until ownership is established.
- Sidecar lane `phase-suite-verification`: after research merge, own the compiler/interpreter/MCP/SPipe/DevHub/Caret per-phase verification matrix and receipts; it may begin only after the merge owner freezes phase inputs and suite commands.
- Merge owner: root Codex session for `.spipe/full-pure-simple-simd-bootstrap`, requirement synthesis, interface freeze, conflict resolution, and intentional-file manifest.
- Final reviewer: root normal/highest-capability Codex after sidecar reports, with a separate verification review before any done mark or push.
- Shared interfaces: `SimdCapabilities`, `SimdBackend`, `SimdLane[T, N]`, `ProcessingIR`, `DatabaseSimdKernels`, and `WebSimdKernels`; research may recommend changes, but implementation fan-out starts only after the merge owner freezes the names in design.
- Manual flow helpers: `step_detect_simd_capabilities`, `step_run_scalar_oracle`, `step_run_simd_backend`, `step_compare_database_results`, `step_compare_web_results`, `step_bootstrap_platform_handoff_readiness`, and `step_verify_deployed_tools`.
- Setup/checker helpers: `setup_simd_fixture`, `setup_database_fixture`, `setup_web_fixture`, `setup_phase_suite_fixture`, `check_simd_equivalence`, `check_simd_performance`, `check_bootstrap_candidate`, `check_phase_component_suites`, and `check_deployed_simple_mcp`.
- Any temporary implementation helper must fail explicitly with `assert(false)` or `fail(...)`; placeholder success is forbidden.
- Generated-manual review owner: root Codex session, with sidecar findings treated as proposals until accepted against source and executable evidence.

## Phase
research-options-ready

## Log
- dev: Created state file with 15 acceptance criteria (type: feature); recorded concurrent dirty-worktree isolation and parallel review boundaries.
- dev: Added AC-16 and the `phase-suite-verification` task for compiler/interpreter/MCP/SPipe/DevHub/Caret checks and all applicable tests at each bootstrap phase.
- research: Completed parallel local/domain research, reconciled current SIMD and bootstrap state, and created three feature options plus three NFR profiles for user selection.
