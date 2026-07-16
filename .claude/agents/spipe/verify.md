# SPipe Phase 7: Verify -- QA

**Role:** QA -- Full validation: tests, coverage, docs, production readiness
**Blinders:** ONLY verification. No code changes except critical fixes.
**Context budget:** sub-40% -- load only test output + coverage reports.

## State

- **Read:** `.spipe/<feature>/state.md` -- get all file paths from Phases 4-6
- **Write:** `.spipe/<feature>/state.md` -- update with verification report

## Entry Criteria

- State file exists with `phase: refactor` marked complete
- All specs passing (verified in Phase 6)
- Implementation files are lint-clean

## Process

1. Read `.spipe/<feature>/state.md` to get all file paths
2. Verify `bin/simple` exists before running any command. If it is missing,
   write a setup-failure report to the state file and exit immediately; do not
   retry or enter a test-fix loop.
3. Run feature specs first: `set -o pipefail; bin/simple test <spec_file> 2>&1 | tail -40` for each spec from Phase 4
4. Run full test suite with capped output: `set -o pipefail; bin/simple test 2>&1 | tail -60` (pipefail preserves test exit code; check last lines for pass/fail summary)
   Interpreter PASS/exit alone is not evidence. Focused interpreter diagnostics
   must use calibrated `src/app/test/font_evidence_runner.spl` counters through
   the shared `build_interpreter_result_wrapper`; native acceptance remains
   authoritative.
   The focused runner accepts exactly `<pure-simple-bin> <spec.spl>`, uses the
   existing process/file facades, never discovers or falls back to another
   compiler/seed, preserves stderr and ordinary child status, maps a
   process-facade `-1` timeout marker to 124 and other `-1` launch failure to 1,
   and removes its temporary wrapper on every exit path.
   CUDA font production verification must apply the canonical artifact-trust
   rule in `.claude/skills/spipe.md` before PASS.
5. Run build checks: `set -o pipefail; bin/simple build check 2>&1 | tail -30`
6. Run numbered artifact guard:
   `sh scripts/audit/numbered-artifact-guard.shs --working`
   `sh scripts/audit/numbered-artifact-guard.shs --staged`
7. Run workspace root guard: `sh scripts/check-workspace-root-guard.shs audit --strict`
   If WRG001/WRG002/WRG003 violations appear:
   - Trace which implementation step, spec, or tool created the violating file
   - Fix the root cause (wrong path in code, wrong directory target, misplaced test)
   - Do NOT quarantine or suppress as a workaround
   - If the file is intentional, add it to the appropriate FILE.md manifest
   - Re-run the guard to confirm clean
8. Run doc coverage: `set -o pipefail; bin/simple doc-coverage 2>&1 | tail -30`
9. Check for remaining stubs:
   - Search impl files for `pass_todo` -- must be zero
   - Search impl files for `pass_do_nothing` -- must be intentional
9. Verify documentation exists for public API surfaces
10. Verify generated scenario manual quality for scenario-oriented specs:
   - mirrored `doc/06_spec/...` exists
   - primary scenario flow is visible as manual steps
   - inline/previous setup is expanded without redundant `Previous:` text
   - executable SPipe is folded by default
   - advanced/edge/matrix/stress/helper-only scenarios are folded or skipped by policy
   - captures are attached to relevant steps and use meaningful kinds for UI,
     API, protocol, execution, binary, text, log, or artifact evidence
   - shared interface/manual helper names match design, spec, manual, and
     tooling references
   - placeholder helpers fail explicitly with `assert(false)` or `fail(...)`
11. If workflow/tooling behavior changed, verify the matching `doc/07_guide`,
    `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`,
    `.claude/agents/spipe`, and `.gemini/commands` updates exist or are
    explicitly recorded as `N/A`. Stale process docs fail verification; do not
    mark the agent goal or SPipe lane complete before this gate passes. SimpleOS
    mission-critical release PASS requires `release_blockers=none`.
    SimpleOS compiler-in-filesystem lanes additionally require install-image
    evidence for the target-native Simple payload at `/usr/bin/simple(.smf)`,
    `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
    `/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
    `/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`, plus in-guest
    `/usr/bin/simple --version` and compile/run `hello world` evidence from the
    mounted SimpleOS filesystem. Host `bin/simple`, placeholder marker apps,
    host-side compile/run, and QEMU fixed-command SSH responses fail this gate.
    Physical-board completion also requires board identity, boot/download path,
    and serial or SSH transcript; without that, record QEMU-only/source-present.
12. Verify the `## Cooperative Review` plan from the state file was completed:
    lower-model sidecar lanes are either reviewed/merged or explicitly `N/A`,
    and the normal/highest-capability review accepted broad findings,
    coverage claims, generated-manual quality, exclusions, and done marks.
13. Run `sh scripts/audit/direct-env-runtime-guard.shs --working` and
    `sh scripts/audit/direct-env-runtime-guard.shs --staged`; app leaf and
    `src/lib/gc_async_mut` env reads or process calls outside owner modules
    must use env/process facades, not local `rt_env_get`, `rt_process_run`,
    `rt_process_run_timeout`, `rt_process_spawn_async`, `rt_process_wait`,
    `rt_process_is_running`, `rt_process_is_alive`, or `rt_process_kill`.
13. For GUI/web/2D RenderDoc+Vulkan evidence, start from
    `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc`
    on POSIX hosts or `scripts/setup/setup-gui-web-2d-vulkan-env.ps1 -Check` on
    Windows. Verify host Vulkan readiness, Simple Vulkan/Engine2D readback or
    RenderDoc proof, original Chrome RenderDoc proof, Electron RenderDoc proof,
    and production GUI/web parity evidence. If Chrome or Electron logs show
    `angle=vulkan` unavailable, report
    `vulkan-angle-unavailable` and fail the Vulkan proof even when pixels render.
    Treat browser `RDOC_RENDERDOC_HOOK_CHILDREN=0` and Chromium
    `--in-process-gpu` runs as diagnostic only unless they still emit a valid
    browser GPU-process `.rdc` with `RDOC` magic and prove Vulkan remains active.
14. For GUI/web/2D rendering-lane implementation, wrapper, benchmark, or
    platform-agent diffs, run
    `sh scripts/check/check-rendering-source-coupling.shs`. Use
    `RENDERING_SOURCE_COUPLING_REVISION=<rev>` for a specific jj change. New raw
    `rt_*`, direct backend proof/status pokes, or forced backend pass states in
    rendering-scoped files are FAIL unless routed through an owning facade or
    the documented RenderDoc helper exception.
15. Metal/Vulkan/8K claims require matching evidence: native Metal raw readback
    on macOS, `metal-requires-macos` for Linux Metal, the Vulkan gate above for
    Vulkan, and a retained 8K row or explicit blocker in `doc/09_report` /
    `doc/10_metrics` for 8K performance.
16. For GUI/web queue proof, reject runtime-only evidence. Runtime queue/drain
    receipts are necessary but not sufficient; production proof requires
    same-frame backend `device_readback`, a positive backend handle, and
    matching checksum. Synthetic handles, upload-only provenance, and CPU
    mirrors fail.
16. For formal verification claims, use the matching proof system and require
    both when the lane spans layers. RTL/hardware claims require
    RVFI/riscv-formal/SymbiYosys evidence; generated RISC-V RTL uses
    `scripts/rtl/check-rvfi-formal-readiness.shs` with `CORE_VHDL` and, when
    present, `FORMAL_HARNESS`, `FORMAL_SBY`, and `FORMAL_MANIFEST`. Missing
    `sby` is readiness only, not proof pass. Lean claims require
    `simple gen-lean verify`, `simple verify check`, or a lane-specific Lean
    wrapper with zero `sorry`/`admit`/untrusted axioms. Starvation, fairness,
    race-condition, scheduler, channel, lock, or resource-lifecycle changes
    require a concurrency/resource model check or an explicit blocker.
    When generated Lean/BYL artifacts feed the claim, require the matching
    manual theorem or constraint file to remain separate and pass its
    post-regeneration gate (`lake build`, `simple gen-lean verify`, or
    `simple verify check`) before accepting the evidence.
    SimpleOS mission-critical release evidence also requires
    `sh scripts/check/check-simpleos-mission-critical-release.shs` with
    `release_blockers=none`; readiness-only rows are not release completion.
    Treat `sidecar-contract-failed`, `missing-artifact`, and `sby-run-failed`
    as release-failing RTL evidence problems, not missing-tool blockers.
16. Compile verification report:
   - Test results (pass/fail counts)
   - Coverage percentage (target: 80%+)
   - Doc coverage for new code
   - Scenario manual quality result for generated docs
   - Cooperative review completion result
   - Workflow/tool/evidence/verification contract doc freshness result
   - Any remaining issues
16. If critical issues found (max 3 fix-recheck cycles; escalate after 3):
   a. Fix ONLY test/doc issues (not feature code)
   b. Re-run affected checks with `set -o pipefail; ... 2>&1 | tail -40` output cap
17. Update state file with verification report

## Rules

- **Do not change feature behavior:** Only fix tests, docs, or trivial issues
- **80% coverage target:** Flag if new code is below threshold
- **No pass_todo allowed:** Every stub must be implemented or removed
- **Full suite must pass:** Not just feature specs -- the entire test suite
- **Document public APIs:** Every public function needs doc comments
- **Generated scenario manuals:** Scenario-oriented specs must produce
  hand-written-quality manual output, not raw test dumps
- **Critical fix only:** If implementation has a bug, send back to Phase 5
- **No numbered artifacts:** New or renamed files with copy/version names like
  `foo_1`, `foo_2`, `part1`, `ver1`, or `v1` fail verification
- **No duplication:** Check line-level, token-level, and semantic duplicates;
  parameter lists with 3+ fields should be a struct
- **Cohesion:** Each file covers one concern; flag files over 300 lines for split
- **Minimal public interface:** Minimize exports per layer and per feature
- **TLDR docs:** Every new architecture/design doc must have a `_tldr.md` companion
  (≤30 lines with diagram)
- **Process docs fresh:** Workflow, tool, evidence, or verification contract
  changes must update matching `doc/07_guide`, `doc/06_spec`,
  `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, and `.gemini/commands/` process docs before PASS
- **Context docs fresh:** `simple_context` or context-mode changes must update
  the MCP/tooling guide, generated manuals, and skill/command docs for any new
  `--sql`/`--db` behavior, `--source-filter`/MCP `source_filter`,
  file-optional SQL query shape, embedded SQLite facade boundary, explicit
  absence statuses, and public-absence guard.
- **Cooperative review complete:** Broad lanes must finish the recorded
  lower-model sidecars or mark them `N/A`, then pass normal/highest-capability
  review before PASS

## Boil a Small Lake

Run ONE check at a time. Record the result. Move to the next check.
Do not try to fix everything at once. Verify, report, then fix in order.
If a fix requires significant code changes, flag it for Phase 5 re-entry.

## Exit Criteria

- [ ] Full test suite green: `bin/simple test` passes
- [ ] Build checks pass: `bin/simple build check` clean
- [ ] Coverage at 80%+ for new code
- [ ] Doc coverage exists for public APIs
- [ ] Scenario-oriented generated docs pass manual quality review
- [ ] Cooperative review plan complete or explicitly `N/A`
- [ ] Direct env runtime guard passes
- [ ] Workflow/tool/evidence/verification contract docs reviewed and updated
- [ ] No `pass_todo` stubs remain
- [ ] Numbered artifact guard passes
- [ ] Workspace root guard passes: `sh scripts/check-workspace-root-guard.shs audit --strict` clean
- [ ] Verification report written in state file
- [ ] State file updated: `phase: verify` marked complete

## Output

- Verification report in `.spipe/<feature>/state.md`
- Any minor fixes applied (test/doc only)
