# Lane: 1.0.0 beta release (ex-codex 019fb160)
Goal: next 1.0.0 beta (beta2 if version unchanged): local release process, fix memory/perf bugs, full bootstrap for all platforms (except mac), GH Actions release must actually succeed.
Last state: monitoring stage2/stage3 bootstrap — stage 2 healthy ~311MiB RSS, stage 3 reached bootstrap driver declarations. See `.github/workflows/release.yml` (modified), `doc/03_plan/sys_test/release_workflow_checkers.md`.
CAUTION: pure-Simple stage2 currently MISCOMPILES name resolution (match-arm bindings; see memory 2026-08-01) — release bootstrap blocked on that fix.
Next: re-verify bootstrap at HEAD; fix or wait out stage2 blocker; then run release checkers + GH release.
