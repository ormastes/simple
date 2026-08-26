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
| Sweep-fix campaign | wave 2 landed | wave 1: `b1ded64c8e4` `8d8d11097a0` `88fe280bb0f` `05b134ac502`; wave 2 (5 parallel agents, 48 specs, ~15 lib bugs): `dddd834f996` `c433e5d091d` `6e7b2eb616a` `9c5595b146d` `4907ce1da97` `e5a10e3ee78` `f65ae4a5f9c` `d9ca9d78b1d` `2f3f215003b`; wave 3: `676241b1db3` `9db7dbb836d` (16 specs); wave 4 (compiler tree, 19 specs + clobber restore): `97c30fce71e` `c8f1bf0c2c2` `bfe408434dd` `179e18fc740` `45b92648ff8` `4345c8e197b` `8e9ef608092`; residue: `doc/08_tracking/bug/unit_sweep_language_and_interpreter_gaps_2026-08-26.md` |

## Open

- Delete `examples/` from simple via a deliberate `--expect-files` landing.
- Sibling repos adopt `data/registry.sdn` + `tests.sdn` format.
- Replace simply's POSIX generator with a `.spl` generator once a released
  binary runs in its CI.
- Stale-API spec drift in browser script specs (`.tag`, `execute_with_type`)
  needs a spec rewrite, not a fixture fix.
- Language/interpreter gaps from the sweep (inline `if/else` expression,
  `_1` lifting, typed empty-array ctor, block-scope leak, `BTreeMap.new`
  intercept, `type X = SharedX` ctor loss) — each needs a compiler change; see
  the bug record above.
