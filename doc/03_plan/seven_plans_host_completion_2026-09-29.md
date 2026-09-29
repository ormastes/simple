# Completion plan for the seven requested items, by host

Date: 2026-09-29
Status: execution plan; implementation completion is not certified.

Execution update (2026-09-29): the user selected Windows first, then macOS,
and requested branch publication and PRs. This ordering supersedes the initial
Windows/Linux ordering below for this execution lane; it does not remove any
supported-host requirement. See the [Windows bootstrap investigation](evidence/seven_plans/windows/bootstrap_readiness_2026-09-29.md).

Subsequent goal update (2026-09-29): Windows first, then Linux through WSL.
This is the current execution order. The earlier macOS request remains recorded
as host scope, but macOS completion must not be inferred from either lane.

## Scope and ownership

Complete the seven items listed below on each supported host. This means seven
distinct feature plans, not seven repeated test runs. Implement shared code once;
verify each host and target combination separately.

Windows native and Linux/WSL are the first execution lanes. macOS, standalone
Linux, FreeBSD, and additional supported hosts remain explicit TODO lanes until
their evidence is available. SimpleOS is a target/guest lane, not evidence that
the development host itself works. Add architecture-specific rows when support
is claimed; an x86_64 result does not certify ARM64 or other architectures.

The execution owner claims one host/item task in the TODO database before editing.
The merge owner integrates shared changes; the final reviewer checks requirements,
host evidence, and the landed commit. Sidecar agents: N/A for this planning change.
Preserve other sessions' work and existing research. Use isolated worktrees when
implementation lanes overlap.

## Status rules

- TODO: work or current host verification remains.
- IN_PROGRESS: an owner has claimed a concrete task.
- BLOCKED: record the exact failing command, cause, next action, and owner.
- VERIFIED: required checks passed for a recorded source commit on this host.
- DONE: verified implementation has landed on main; evidence covers the landed
  content, generated manuals are current, and no required requirement remains open.
- N/A: permitted only for a documented unsupported capability with an accepted
  scope decision. Missing runners, hardware, or tests are BLOCKED, not N/A.

An open PR, a design document, source inspection, or a passing helper test alone
does not establish DONE. Windows and WSL evidence must be kept separate.

## Host tracking matrix

All cells start TODO for completion certification, even where implementation
already exists. This is not a claim that each feature is unimplemented.

| Item | Windows native | Linux/WSL | Linux native | macOS | FreeBSD | SimpleOS guest/target |
|---|---|---|---|---|---|---|
| 1. Platform unification, parser, dynload, release | TODO | TODO | TODO | TODO | TODO | TODO |
| 2. SCV + jj + GitHub textual databases | TODO | TODO | TODO | TODO | TODO | TODO: scope admission |
| 3. Typed DataFrame collections and optimizer | TODO | TODO | TODO | TODO | TODO | TODO |
| 4. mold-based MDSOC++ linker | TODO | TODO | TODO | TODO | TODO | TODO |
| 5. Kernel/extension aspects and binary size | TODO | TODO | TODO | TODO | TODO | TODO |
| 6. Compile optimization | TODO | TODO | TODO | TODO | TODO | TODO |
| 7. Profile-based switchable container algorithms | TODO | TODO | TODO | TODO | TODO | TODO |

For additional hosts, create all seven child tasks when that host enters the
supported matrix. Unsupported OS/object-format combinations need an explicit
capability contract and deterministic diagnostic before scope can be closed.

## 1. Platform unification, parser sharing, environment-optimized dynload, SimpleOS release

Requested plan: **Simple Platform Unification, Parser Sharing,
Environment-Optimized Dynload, and SimpleOS Release Architecture**.

Related references:
[runtime unification](../01_research/runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md),
[dynload architecture](../04_architecture/compiler/environment_optimized_dynamic_libraries.md),
[dynload plan](compiler/environment_optimized_dynamic_libraries.md).

- Locate the canonical umbrella document and map every retained requirement to
  implementation, tests, and host capability; retain its title/path in evidence.
- Complete shared parser ownership and check compiler/interpreter/tooling syntax
  parity. Platform adapters must expose documented capability differences.
- Complete target/CPU/environment selection, ABI validation, deterministic fallback,
  missing-library errors, and cache invalidation for dynamic loading.
- Build immutable release candidates with manifests identifying compiler, runtime,
  target, and optional providers; execute the release/bootstrap path for each host.
- Verify equivalent parser fixtures across supported execution paths, load a valid
  provider, reject incompatible providers, and boot the claimed SimpleOS target.

Done gate: requirement traceability, host parser/runtime tests, dynamic-provider
tests, and reproducible release/boot evidence all pass.

## 2. Simple distributed textual databases: SCV + jj + GitHub

References: [research](../01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md),
[architecture](../04_architecture/simple_distributed_textual_databases.md),
[system test plan](sys_test/simple_distributed_textual_databases.md).

- Finish schema validation, stable record identity, deterministic serialization,
  indexing/query behavior, and transactional local updates.
- Complete SCV integration with jj history and GitHub synchronization using the
  documented conflict and credential boundaries.
- Exercise two isolated clones: independent edits, conflicting edits, resolution,
  offline changes, interrupted synchronization, retry, and recovery without loss.
- Verify host-specific paths, case sensitivity, Unicode, line endings, file locks,
  and atomic replacement. Use a designated test remote for synchronization tests.

Done gate: convergence and recovery assertions pass with actual database contents
and history inspected; remote authorization and secrets remain outside artifacts.

## 3. Simple Typed DataFrame-able Collections and Query Optimizer

References: [collection plan IR](../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md),
[system test plan](sys_test/collection_planner.md).

- Audit and close the research P0 semantic prerequisites before enabling optimized
  execution: array-map resolution, closure ABI, any/all, native Dict insertion,
  and collection behavior across backends.
- Complete typed collection/query extraction, physical-plan selection, and actual
  lowering; verify each retained filter, projection, grouping, aggregation, and
  join requirement against the reference execution path.
- Preserve ordering, duplicates, null/optional values, ownership, and error behavior
  wherever the language contract requires them.
- Measure representative cardinalities and skew; expose selected plans and reasons
  so a test proves which implementation ran.

Done gate: semantic equivalence, real lowered-plan execution, and retained NFR
targets pass on every claimed backend/host. An advisory planner alone is incomplete.

## 4. Simple Linker: mold-Based MDSOC++ Architecture and Implementation Plan

Reference: [linker research and plan](../01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md).

- Map the retained MDSOC++ linker layers to implemented owners and interfaces.
- Complete symbol resolution, relocations, archives, dead stripping, dynamic
  dependencies, diagnostics, and deterministic output required by the plan.
- Record object-format/backend support explicitly: ELF, PE/COFF, and Mach-O must
  each have an admitted implementation or an accepted unsupported scope decision.
  Do not infer Windows/macOS support from a successful ELF/mold invocation.
- Test small fixtures through executable startup, missing/duplicate symbols,
  relocation failures, shared libraries, and stripped output.
- Link and execute the self-hosted compiler and representative applications;
  record link time, peak memory, output size, and correctness against a baseline.

Done gate: executable outputs and diagnostics meet each admitted target contract,
with real linker integration and the plan's performance requirements verified.

## 5. Kernel/extension aspect dynload for Simple size

Related references: [optional provider size architecture](../04_architecture/compiler/perf/runtime_optional_provider_binary_size_optimization.md),
[executable size architecture](../04_architecture/compiler/optimization/executable_size_reduction.md).

- Identify the canonical kernel/extension aspect requirements and map mandatory
  core functionality versus optional providers and their dependency closures.
- Complete aspect selection, optional-provider packaging/loading, ABI checks,
  failure handling, and target capability manifests.
- Verify minimal programs exclude unused extensions using binary sections,
  symbols, and dependency manifests; verify enabling an extension restores behavior.
- Measure stripped/unstripped size and startup/RSS for minimal and representative
  applications using the same compiler, target, and build mode.
- Exercise missing/incompatible extension failures and supported lifetime behavior.
  Respect kernel/driver layering; do not introduce MDSOC+/ECS there by default.

Done gate: actual dependency exclusion and extension functionality are demonstrated,
and the retained size budgets pass without correctness regressions.

## 6. Simple compile optimization: final research, architecture, implementation plan

Related reference: [persistent package/module index](../04_architecture/compiler/perf/persistent_package_module_index_compile_optimization.md).

- Locate the canonical final plan and build a requirement-to-stage inventory;
  the related index document is not a substitute for the full requested scope.
- Establish clean build, warm build, no-op rebuild, and single-module-edit baselines
  with source/toolchain hashes, fixture sizes, timing, and peak RSS.
- Complete retained indexing, caching, dependency tracking, and invalidation work.
  Measure parse/type/lowering/codegen/link stages to identify remaining costs.
- Verify semantic invalidation after imports, configuration, target, compiler,
  generated files, and public interfaces change; test corrupt-cache recovery.
- Confirm optimized builds produce behavior equivalent to uncached builds and
  pass bootstrap, core runtime, MCP, and LSP requirements where affected.

Done gate: retained end-to-end compile-time and memory targets pass, cache
correctness is demonstrated, and no required optimization remains advisory only.

## 7. Profile-based, switchable container algorithms

References: [architecture and implementation status](../04_architecture/compiler/profile_switchable_container_algorithms.md),
[system test plan](sys_test/profile_switchable_container_algorithms.md),
[agent tasks](agent_tasks/profile_switchable_container_algorithms.md),
[P6 research](../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md).

Planning snapshot: the current architecture reports adaptive set/map implementations,
attribute parsing, collection profile capture/admission, and an advisory selector.
It also records missing execution proof, typed extraction/lowering work, broader
metrics, generic coverage, and cross-backend evidence. Reconcile these statements
against the claimed source commit; do not reuse the earlier blanket conclusion
that no attribute or profile implementation exists.

- Prove each container's attribute selects the actual representation/algorithm;
  two instances with different attributes must remain independent.
- Finish supported generic set/map coverage, typed site identity, CollectionPlan
  extraction, semantic/target guards, and optimizer-to-MIR lowering.
- Complete applicable P6 workload measurements and their consumption. Distinguish
  collection feedback from unrelated function-hotspot .sprof counters.
- Execute a two-run scenario: collect workload A, save/admit its profile, then run
  the same attributed program using feedback and observe the selected algorithm.
- Repeat with a different admitted workload profile B whose measured characteristics
  justify a different choice. Check identical logical results and explain selection.
- Reject stale source/schema/target or mismatched workload identity; verify explicit
  attribute precedence, auto fallback, atomic publication, and append failure safety.
- Test representation transitions, collision-heavy input, ownership/iteration
  contracts, bounded policies, concurrent capture boundaries, and instrumentation cost.

Done gate: native Windows and Linux/WSL each demonstrate attribute -> measurement
-> profile -> guarded selection -> actual execution, with generic correctness and
retained NFRs. Parser rewrites or a selector unit test alone cannot close this item.

## Execution order and host-specific checks

1. Register seven parent tasks and host/item children; claim owners and reconcile
   existing artifacts, PRs, TODOs, and source state before changing implementations.
2. Establish an admitted pure-Simple self-hosted runner on Windows and Linux/WSL.
   Rust seeds are bootstrap-only. Record bootstrap failures as blockers.
3. Close item 1 foundations, item 3 P0 prerequisites, and item 4 linker support;
   then integrate item 5 and item 6 against those contracts. Item 2 can proceed
   independently. Finish item 7 lowering after item 3 readiness gates pass.
4. Finish and verify shared code plus Windows and Linux/WSL adapters. Keep evidence
   separate even when both hosts execute the same test suite.
5. Run remaining host tasks using the same requirement IDs and fixtures. macOS
   checks Mach-O/dylib behavior and supported architectures; Windows checks PE/DLL,
   paths, locks, and command shells; Linux checks ELF/shared libraries and filesystem
   semantics. A WSL run does not certify native Linux-specific integration.
6. For FreeBSD from Linux, use `sh scripts/check/check-freebsd-bootstrap-qemu.shs
   --smoke`, then the required `--full` pass. Preserve guest logs and target identity.
7. Review evidence, land verified changes through PRs, and update only the host/item
   tasks whose required scope is complete. Publish releases only after verify PASS.

## TODO database and evidence contract

This document does not itself insert or close database records. The execution
owner must use the repository's canonical TODO interface, reuse existing records,
and link the resulting IDs here or in a companion receipt. Do not invent task IDs.

Each host/item record must include:

- Item number, host/architecture, target triple, owner, state, and dependencies.
- Canonical plan and retained requirement IDs, implementation paths, spec paths,
  generated manual paths, and measurable NFR targets from approved requirements.
- Source commit, runtime provenance, commands, exit codes, logs, fixture identity,
  baseline/results, limitations, blocker/next action, and PR/landed commit.

Store per-host execution reports under
`doc/03_plan/evidence/seven_plans/<host>/<item>/` and bulky run artifacts under
`build/test-artifacts/seven_plans/<host>/<item>/`. These are planned paths.
Require durable CI/artifact links for evidence referenced after local cleanup.

## Verification and stopping rules

Apply the repository verification gates for the changed scope: real SPipe
assertions, requirements traceability, current generated manuals, no stubs, env
facade guards, and zero executable `_spec.spl` files in `doc/06_spec`.
Compiler/core/lib or MCP/LSP changes require the mandated compiler/lib/MCP/LSP
checks, interpreter stdio integration, and affected runtime/native/package smokes.
Record exact commands using the admitted host runtime; do not substitute the seed.

Run each acceptance check once for the implementation under review. Re-run only
when a relevant change invalidates its evidence or a required gate demands it.
After three fix/verify cycles, report the remaining blocker and stop that lane.
Never mark missing host evidence as a pass. The seven-item program is complete
only when every required host/item cell is DONE or has an accepted scope exclusion.
