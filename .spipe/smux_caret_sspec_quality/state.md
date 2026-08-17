# Feature: smux-caret-sspec-quality

## Raw Request

`Caret and smux SSpec quality; audit upstream-equivalent work and continue only a genuinely unfinished criterion.`

## Task Type

quality

## Refined Goal

Bring the smux and LLM Caret spec suites onto Modern SSpec with real oracles,
so no spec in the lane can be permanently RED under the fail-closed
zero-examples gate while printing `PASS`, and add fail-closed system-level
coverage that fails if the legacy shape or mirror drift reappears.

## Acceptance Criteria

- AC-1: every legacy `fn test_*` + `print("PASS"/"FAIL")` spec in the lane is converted to `describe`/`it` blocks with `expect(...)` oracles, with no surviving `main()` driver.
- AC-2: both duplicate test trees (`test/01_unit/**` and `test/unit/**`) are updated identically and stay byte-identical, so `check-test-tree-divergence` gains no new offender.
- AC-3: the zero-examples gate is cleared — `executed` is non-zero for every converted file, and every original check survives as an example.
- AC-4: a fail-closed step-based system SSpec traces REQ-SSQ-001..005 and NFR-SSQ-001, discriminates modern from legacy before judging real files, and treats a missing file as a failure rather than a skip.
- AC-5: `doc/06_spec` carries the mirrored Markdown manual only and contains no executable `.spl` for this lane.
- AC-6: any grammar/compiler defect surfaced by the conversion is filed as a concrete bug rather than silently normalized into a workaround.
- AC-7: the legacy system spec `test/03_system/tools/smux_system_spec.spl` is converted to Modern SSpec with REQ-traced `it` blocks and visible `step(...)` flows.

## Status

| AC | State | Evidence |
|---|---|---|
| AC-1 | DONE | 41 `fn test_*` converted across 2 specs; 0 `fn test_*`, 0 PASS/FAIL prints, 0 `main()` remain |
| AC-2 | DONE | `cmp` clean on both pairs; `check-test-tree-divergence-delta` PASS — 0 introduced |
| AC-3 | DONE (seed-evidenced) | `executed=20/20/21/21`, `failed=0` in all four files |
| AC-4 | DONE (seed-observed) | `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`, 13 examples, `executed=13 passed=13 failed=0`; admitted evidence TEST_BLOCKED |
| AC-5 | DONE | `doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md`, Markdown only |
| AC-6 | DONE | `static_factory_method_chain_wrong_value_2026-08-16.md` and `module_var_stale_in_it_closure_2026-08-16.md` filed |
| AC-7 | DONE (seed-observed) | 56 `fn test_*` -> 56 `it` across 13 REQ groups; `executed=56 passed=56 failed=0`; 858 -> ~700 lines |

## Upstream audit

The **LLM Caret half was already complete upstream** and was not redone. A sweep
of every caret `*_spec.spl` at `origin/main` for the legacy pattern (`fn test_*`
with zero `it` blocks) returned **zero hits**. Only the smux half was genuinely
unfinished, recorded in
`doc/08_tracking/bug/smux_legacy_specs_zero_examples_red_2026-08-16.md`.

## Evidence status — TEST_BLOCKED for the new system spec

Every verdict in this lane came from the Rust bootstrap seed, the only binary
in-tree implementing a `test` subcommand. It is **not** an admitted pure-Simple
runner, so none of these runs is acceptance evidence; they are recorded as
development observations. No admitted runner exists here:

- tracked self-hosted `release/x86_64-unknown-linux-gnu/simple` segfaults in `test` (exit 139)
- `bootstrap/stage1|2|3/simple` expose no `test` and cannot lower the SSpec DSL
- `build bootstrap` dies inside Stage 1 without a verdict

Upstream corroboration:
`doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.

No placeholder pass was recorded anywhere in this lane.

## Open / not claimed

- Two compiler defects are filed OPEN and worked around, not fixed here:
  `static_factory_method_chain_wrong_value_2026-08-16.md` and
  `module_var_stale_in_it_closure_2026-08-16.md`.
- Pre-existing `check-test-tree-divergence` red (828 offenders) stepped over on
  a delta-PASS, recorded in
  `doc/08_tracking/bug/test_tree_divergence_preexisting_red_2026-08-16.md`.

## Artifacts

- `test/01_unit/os/smux_spec.spl` (+ `test/unit/` mirror)
- `test/01_unit/os/smux/smux_dashboard_spec.spl` (+ `test/unit/` mirror)
- `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`
- `test/03_system/tools/smux_system_spec.spl` (converted, 56 examples)
- `doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md`
- `doc/03_plan/sys_test/smux_caret_sspec_quality.md`
- `doc/07_guide/infra/sspec_legacy_migration.md` (worked example 3)
- `doc/00_llm_process/feature_expert/smux_caret_sspec_quality/skill.md`
