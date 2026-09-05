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
| Full `test/01_unit` sweep → dashboard | done | 8,851 files verdicted — 118,684 passed / 4,579 failed / 2,818 skipped / 11 pending across 48 groups; 1,597 files have >=1 failure; 42 files excluded as known hangs (no verdict in a 300s per-file budget), named in the JSON `note`. Published as simply `b88073f` |
| Sweep-fix campaign | wave 2 landed | wave 1: `b1ded64c8e4` `8d8d11097a0` `88fe280bb0f` `05b134ac502`; wave 2 (5 parallel agents, 48 specs, ~15 lib bugs): `dddd834f996` `c433e5d091d` `6e7b2eb616a` `9c5595b146d` `4907ce1da97` `e5a10e3ee78` `f65ae4a5f9c` `d9ca9d78b1d` `2f3f215003b`; wave 3: `676241b1db3` `9db7dbb836d` (16 specs); wave 4 (compiler tree, 19 specs + clobber restore): `97c30fce71e` `c8f1bf0c2c2` `bfe408434dd` `179e18fc740` `45b92648ff8` `4345c8e197b` `8e9ef608092`; wave 5 (~34 specs, 4 slices): slice0
`7971f2bffbb` `6a02c0f8c4c` `745540b000e` `5c219ddf6d2`, slice1 `a41ef500f83`
`64f8098101d` `11c816c21d9` `06fa37dc08f` `284ce63b0ac`, slice2 `dc58fec5f1b`
`8da31723373`, slice3 `e5a7528f063` `46bb8524167` `1f3c1225f8b`
`aa0fbd39bdf`; residue: `doc/08_tracking/bug/unit_sweep_language_and_interpreter_gaps_2026-08-26.md` |

## Open

- ~~Delete `examples/` from simple via a deliberate `--expect-files` landing.~~
  **Partly done 2026-08-27.** Migration verified first: after simply sync commit
  `9dca83d` (102 files simple had moved forward on since the 08-25 import — the
  freeze was violated by commits on 08-26/08-27), 1,798 of 1,799 tracked entries
  are byte-identical; the last is the `simple_cuda_example` gitlink, already
  vendored in simply as 96 files. **Full retirement is blocked:** 732 non-doc
  files (364 `test/`, 182 `scripts/`, 132 `src/`) build/test/execute
  `examples/**` — `examples/09_embedded/` is SimpleOS boot/arch product code,
  `examples/05_stdlib/spipe/` is the SPipe source mirror. Only 118 unreferenced
  files were deleted (+ the gitlink and its `.gitmodules` stanza), and
  `examples/README.md` now points at simply and explains what remains. Follow-up
  is a MOVE task: relocate the load-bearing trees out of `examples/` and update
  their referrers, then the rest can go. Landed as PR (see below).
- Sibling repos adopt `data/registry.sdn` + `tests.sdn` format.
- Replace simply's POSIX generator with a `.spl` generator once a released
  binary runs in its CI.
- Stale-API spec drift in browser script specs (`.tag`, `execute_with_type`)
  needs a spec rewrite, not a fixture fix.
- Language/interpreter gaps from the sweep (inline `if/else` expression,
  `_1` lifting, typed empty-array ctor, block-scope leak, `BTreeMap.new`
  intercept, `type X = SharedX` ctor loss) — each needs a compiler change; see
  the bug record above.

## Sweep close-out (2026-08-26)

The sweep completed at 8,851 verdicted files after a runner defect was worked
around: `bin/simple test --json <many files>` stops permanently at the first
spec that hangs (the run died at file 1,340,
`test/01_unit/app/ui/semantic_backend_helpers_spec.spl`, and no later file ever
got a verdict). `--timeout <seconds>` gives each file its own budget, emits
`UNVERIFIED <path>: TIMEOUT`, and continues. Separately — and **not** caused by
`--timeout`, as this note previously claimed — `--no-session-daemon` with two or
more positional paths runs only the FIRST one and exits 0: `parse_child_run` in
`src/app/test_runner_new/test_runner_single.spl` did
`if not arg.starts_with("-") and path == "": path = arg`, so later paths fell
through with no branch and no warning, and the lane's greenwash hardening is all
per-file so none of it could fire for a path discarded at parse time. Every
in-tree caller passes exactly one path, so no CI or gate green was invalidated;
the exposure was interactive/agent batching. Record:
`doc/08_tracking/bug/test_runner_single_lane_drops_extra_paths_2026-08-27.md`;
fixed to fail closed in PR #66. The 42 hangs cluster in `lib/crypto/*_kat` and `lib/common/crypto`
perf specs.
