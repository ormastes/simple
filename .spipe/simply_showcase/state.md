# Feature: simply showcase — whole-earth software registry + test-driven dashboard

## Raw Request

Make a GitHub repo like `simply` for whole-earth software in Simple: showcase
site, implementation plans, scripts to update pages daily, feature/NFR lists
with done percentage, migrate the examples folder, standardized dashboards per
project, prevent recursive repo inclusion, dashboard produced by modern sspec
tests (future-impl sspec tests, test status links, feature grouping + done %),
share the glass theme with SimpleOS, then run the full unit sweep and fix.

## Task Type

feature

## Refined Goal

One truthful capability registry (Wave 0 of the whole-world software map)
rendered as a dashboard whose test panel is produced verbatim by
`simple test --json`, with completion criteria and per-row test lists, and a
recursion guard between simply and simple.

## Status (2026-08-26)

| Step | State | Evidence |
|---|---|---|
| Research map | done | `doc/01_research/domain/whole_world_software_implementation_map_2026-08-25.md` |
| simply repo + site | done | https://github.com/ormastes/simply · https://ormastes.github.io/simply/ |
| Recursion guard | done | simply generator fails on nested `.git`; simple `.gitignore` blocks `examples/simply/` |
| `planned()` marker | done | `spec.spl` + seed BDD arm; spec `test/01_unit/app/test_runner_group_json_spec.spl` (`db45479c256`) |
| `test --json` + groups/done_pct | done | main/client/Rust lanes (`193af515043`, `590a2676e8e`) |
| Seed shadowing fix | done | redeployed seed built from origin/main; strace 0 foreign opens |
| Completion criteria + test lists | done | simply `doc/plan/completion_criteria.md`, `data/tests.sdn` (`80ffc46`) |
| Full `test/01_unit` sweep → dashboard | in progress | 8,807 files; results go to simply `data/test_results.json` |
| Sweep-fix campaign | in progress | landed: `b1ded64c8e4` sha1_x4, `8d8d11097a0` expect_not/imports, `88fe280bb0f` tmux, `05b134ac502` node-id fixtures |

## Open

- Delete `examples/` from simple via a deliberate `--expect-files` landing.
- Sibling repos adopt `data/registry.sdn` + `tests.sdn` format.
- Replace simply's POSIX generator with a `.spl` generator once a released
  binary runs in its CI.
- Stale-API spec drift in browser script specs (`.tag`, `execute_with_type`)
  needs a spec rewrite, not a fixture fix.
