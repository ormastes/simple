# Feature: restart12-render-cli-runtime-selection

## Raw Request
Resume the exact Rendering CLI lane, complete the focused implementation,
add future-executable modern SSpec/manual coverage, update lane knowledge, and
integrate honestly without Rust-seed evidence or Phase 4 work.

## Refined Goal
Remove implicit native-build worker fallback to the canonical Rust seed or
unchecked `bin/simple`, fail closed before spawn when no configured/invoking
candidate remains, and retain executable REQ-RENDER-CLI-002 coverage for the
next admitted pure-Simple full CLI.

## Acceptance Criteria
- AC-1: Runtime selection considers only available `SIMPLE_BINARY`,
  `SIMPLE_BIN`, and invoking-executable candidates, in priority order.
- AC-2: Canonical `src/compiler_rust/target/` candidates are rejected.
- AC-3: Empty selection returns nonzero before environment export or worker
  spawn; there is no implicit `bin/simple` fallback.
- AC-4: Unit, native-probe, and modern step-based system coverage use real
  assertions with REQ-RENDER-CLI-002 traceability.
- AC-5: The mirrored manual, system-test plan, rendering CLI guide, and
  native-build feature-expert wiki describe the same fail-closed contract and
  honest runtime blocker.
- AC-6: No executable `.spl` is placed under `doc/06_spec`; changed-file,
  direct-env, layout, and diff guards pass once before integration.
- AC-7: Commit/push is serialized under
  `/mnt/data/tmp/simple-main-restart12-push.lock`, rebased linearly, pushed once
  without force, and proven reachable from refreshed `origin/main`.

## Scope Exclusions
- Stage 4 construction, deployment, or admission.
- Cached render carrier construction or sparse 8K execution.
- Phase 4 rendering, presentation, physical scanout, or performance claims.
- Authentication of arbitrarily renamed executables.
- Shared global Codex/Claude/Gemini skills owned by other panes.

## Runtime Status
- Source implementation: complete.
- Test status: `TEST_BLOCKED` (qualified pure-Simple full CLI unavailable).
- Qualified full-CLI test/maintenance/docgen runtime: unavailable.
- Admitted Stage 2: compile/native-build only; three retained-surface probe
  cycles exhausted and not rerun.
- Known-bad `release/` full CLI and all Rust seeds: inadmissible evidence.
- System SSpec/manual: present and future-executable; `TEST_BLOCKED`, not PASS.

## Phase
implementation-complete-TEST_BLOCKED

## Log
- recovery: preserved isolated worktree based on `origin/main` f6cadcc36aff.
- recovery: removed canonical Rust-seed and unchecked `bin/simple` fallback.
- recovery: added unit, native-probe, and modern SSpec coverage with real
  assertions and REQ-RENDER-CLI-002 traceability.
- recovery: synchronized only the lane manual, test plan, guide, state, and
  native-build feature-expert wiki.
