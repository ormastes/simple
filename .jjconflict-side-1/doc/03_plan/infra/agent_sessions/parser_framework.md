# Lane: Parser Framework (ex-codex 019fb81d)
Goal: `$dev` with agent teams — implement `parser_framework_plan.md` (owned under `.spipe/parser_framework/state.md`, `doc/03_plan/platform/structural_compute/parser_framework_plan.md`, and this lane docs) across parser-framework artifacts in this repo.

## Completed in this lane handoff
- Added `auto` mode constant in public parse contracts and exports.
- Wired runtime dispatch to treat `PARSE_MODE_AUTO` as an explicit selection path with deterministic CPU fallback behavior and measurable hooks.
- Replaced parser-framework placeholder seams in:
  - `auto_profile.spl` (`select_parse_mode`)
  - `structural_index.spl` (deterministic UTF byte classification scaffold)
  - `incremental.spl` (deterministic fallback plan)
  - `parallel_lex.spl` (state composition and output emit scaffolds)
- Added deterministic system-spec coverage in `test/03_system/app/compiler/feature/parser_framework_spec.spl` for:
  - `auto` runtime normalization
  - malformed UTF rejection
  - parse-runtime error handling for missing/unknown mode
- Mirrored those additions in `doc/06_spec/03_system/app/compiler/feature/parser_framework_spec.md`.

## Open blockers / next steps
- This worktree is the main repo only; the parser-framework implementation that owns full SIMD/GPU/incremental parity (`~/dev/pub/simple-parser-framework-impl`) is still the lane’s primary follow-up source.
- Common-model modules under `src/lib/common/structural/parse` remain `wave-1` baseline for many advanced AC-4/5/6 behaviors.
- AC-9/AC-10 remain open for full delimiter/quote/indent continuation, chunk-boundary determinism, incremental mapping/invalidation reuse proofs, and measured auto crossover evidence.

## Current best-next action
- Continue in this lane by advancing `doc/03_plan/infra/agent_sessions/parser_framework.md` into the next implementation pass once Spark budget is available, prioritizing AC-10 operator-visible coverage and removing placeholder claims from architecture/implementation lanes where possible.
