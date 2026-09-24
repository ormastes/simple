<!-- codex-research -->
# Windows Full Bootstrap and Toolchain Suite — Local Research

## Scope and Current State

The requested lane spans the Windows bootstrap trust chain, compiler/interpreter checks, essential CLI tools, MCP/LSP, SPipe, DevHub, Caret, IDE, T32 MCP/CLI, staged publication, and local deployment/rollback. The SPipe intake is `.spipe/windows_full_bootstrap_toolchain_suite/state.md` with AC-1 through AC-24. No exact-name research, requirements, architecture, design, or test-plan artifacts existed before this research.

The checkout is based on `main@origin` commit `e74e4f6a`, with one rebased local Windows commit and a broad working-copy change above it. Six jj conflicts must be resolved before execution evidence is trustworthy. The pre/post sync tracked-file guard increased from 133,959 to 135,613 files, so no unexpected reduction occurred.

## Canonical Bootstrap Path

There is no Stage-1-only Windows stop. `scripts/bootstrap/bootstrap-windows.cmd` is a Windows launcher that selects Git Bash/MSYS2 and forwards through `bootstrap-windows.sh` to the shared bootstrap driver. The smallest authoritative first promotion is:

```text
scripts/bootstrap/bootstrap-windows.cmd --msvc --full-bootstrap --stop-after-stage2 --mode=dynload --output=<isolated-absolute-output>
```

This receipt-free trust-root lane produces Stage 1 seed evidence and an admitted Stage 2 compiler. It excludes deploy, full-CLI, and resume behavior. Each run needs isolated output/cache paths and exact path/hash/source/provenance capture.

Stage 3 and Stage 4 require typed `simple-bootstrap-planner-admission-v2` receipts. The canonical producer is `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`, bound to the exact admitted parent compiler, bootstrap output, target, and typed reason. Stage 3 resumes with `--resume-stage3-from-admitted=<output>`; Stage 4 requires a fresh Stage 4 receipt and resumes with `--resume-stage4-from-admitted=<output> --deploy`.

The existing build tree is not admissible: a Stage 1 executable and an old full binary exist, but the current Stage 2 directory/receipt and Stage 3/4 provenance chain are absent. Old partial transcripts cannot authorize promotion.

## Phase and Tool Evidence

- `doc/07_guide/tooling/bootstrap_phase_verification.md` and `bootstrap_phase_feature_matrix.md` require admitted absolute binaries, SHA-256, generation/provenance, complete rows, and fail-closed blocked/unsupported metadata.
- `doc/07_guide/infra/phase_snapshots.md` requires immutable lineage-named snapshots; Phase N+1 must not consume mutable `bin/simple` or a moving stage path.
- `doc/07_guide/tooling/frozen_bootstrap_worktree.md` requires frozen/private source state and decides success from artifacts rather than log existence.
- `scripts/check/build-and-verify-tools-with.shs <compiler>` provides an admitted-compiler tool proof covering compiler version, MCP/LSP initialization, T32 version/init, and `sj` help.
- `scripts/bootstrap/stage4-tooling-matrix.shs` is the full Stage 4 DAG for compiler/lib/MCP/LSP checks, bootstrap/core/full tests, essential/tooling tests, protocol/stdio behavior, SPipe docgen, native builds, and editor dispatch.
- `scripts/check/check-bootstrap-essential-tools-smoke.shs <stage4-binary>` is the mandatory bounded post-bootstrap gate for test runner, lint, duplicate-check, and aggregate markers.
- Interpreter evidence uses `--mode=interpreter --no-session-daemon --sequential --no-db --no-cache --assert-ran --fail-fast` where supported, with canonical authenticated execution rather than stdout-only PASS text.

## Named Suite Entry Points

- MCP/LSP: check `src/app/mcp` and `src/app/simple_lsp_mcp`; run `test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`; prove initialize, initialized, tools/list, and representative `simple_pipe`/`simple_search` requests. Native package builds are required when packaging/deployment changes.
- IDE: interpreted entry `src/app/ide/main.spl`; primary smoke includes `--help` and a representative edit/check interaction.
- DevHub: `bin/devhub <command>` and `bin/devhub --gui`; top-level help has a known incomplete banner and must not be overclaimed.
- Caret: Windows launcher `bin/cs.cmd` delegates through `bin/simple.cmd` to `src/app/llm_caret/cs_main.spl`; focused suites are documented in `doc/07_guide/app/llm/llm_caret_agent_teams.md`.
- T32: interpreted `src/app/t32_mcp_server/main.spl --help|--version`; native Windows wrappers require the exact deployed MSVC executables. TRACE32-dependent tests remain blocked when the provider is absent, but version/init checks are hardware-free.
- SPipe: verify `/sp_dev` routing, representative execution/docgen, generated-manual quality, and zero executable `*_spec.spl` files under `doc/06_spec`.

## Conflict Research

The six post-rebase conflicts have deterministic upstream-compatible resolutions:

1. `scripts/bootstrap/bootstrap-windows.cmd`: both sides are blob-equivalent; retain the current WSL-safe 35-line launcher without the conflict envelope.
2. `test/01_unit/os/tty/pty_host_capability_spec.spl`: both sides are equivalent; retain the full CRLF PTY round-trip and `is_running` coverage.
3. `src/compiler/80.driver/driver_aot_native_output.spl`: use current `main`; it is the strict superset with exact I/O, direct disk-byte hashing, receipt reasons, and richer diagnostics.
4. `scripts/check/check-push-must-pass.shs`: use current `main`; it contains the local Windows rows plus newer ref-aware wiring checks, while combining hunks would duplicate cases.
5. `config/check/must_check_gates.sdn`: use current `main`; it has ledger v3 columns and newer gates, while the local side is an obsolete schema.
6. `doc/08_tracking/bug/windows_native_capsule_receipt_invalid_blocks_every_native_build_2026-09-03.md`: use current `main`; it includes the older resolution plus newer issue context.

## Windows Constraints and Gaps

- Git Bash/MSYS2 is required; System32/WindowsApps WSL bash is rejected.
- PATH translation, GNU Rust triple selection, and PowerShell junction behavior must be normalized before bootstrap.
- Linux cross-build evidence cannot admit a Windows compiler. The proposed separate-host plan is design input, not proof of Windows Phase 2/3.
- The dated deployment atomicity review reports a missing transaction wrapper and mixed-generation risk; current source must be rechecked before deployment.
- The knowledge registry has no exact feature route. The selected longest-prefix owners are compiler pipeline, runtime/memory/I/O, and app/editor/tooling; creation/selection of a feature expert remains a knowledge-update requirement.

## Research Conclusion

Use a strict staged promotion: resolve conflicts, freeze the lane, run the combined Stage 1/Stage 2 trust-root build, verify compiler/interpreter/tools against its exact hash, publish only that admitted head, then produce typed receipts for Stage 3 and Stage 4. Run the full integrated matrix and atomic deployment/rollback only against the final unchanged Stage 4 subject.

