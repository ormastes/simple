# Feature Expert — simply showcase (whole-earth software registry + site)

## Role

Own the knowledge around the `ormastes/simply` satellite repo: the whole-world
capability registry, the generated dashboard site, the examples migration, and
the recursion guards between simply and this repo.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)

## Feature Links

- Research (map): [`doc/01_research/domain/whole_world_software_implementation_map_2026-08-25.md`](../../../01_research/domain/whole_world_software_implementation_map_2026-08-25.md)
- Guide: [`doc/07_guide/infra/simply_showcase_repo.md`](../../../07_guide/infra/simply_showcase_repo.md)
- External repo: https://github.com/ormastes/simply (site https://ormastes.github.io/simply/)
- Design (in simply): `doc/plan/design.md`
- Theme source of truth here: `src/lib/common/ui/glass/` (simply `docs/glass.css` mirrors it)

## Current state (2026-08-25)

- simply created: registry `data/registry.sdn` (69 rows I01–I38 + A01–A31,
  `id|group|name|F|U|P|done|status|sspec`), POSIX generator
  `scripts/update_site.sh` with nested-checkout recursion guard (tested FAIL
  exit 1), glass Pages site (main `/docs`), daily-update workflow, examples
  corpus copied from this repo.
- This repo: `.gitignore` blocks `examples/simply/` + `simply/`; `examples/`
  is frozen here (deletion deferred to an `--expect-files` guarded landing).

## Open work

1. DONE 2026-08-26 — `planned(name, reason)` marker: runtime body in
   `src/lib/nogc_sync_mut/spec.spl`, seed BDD arm in
   `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` (counts as
   pending, never pass/fail). Spec:
   `test/01_unit/app/test_runner_group_json_spec.spl`.
2. DONE 2026-08-26 — `test --json` alias (json_wrapper.spl) and
   skipped/pending totals in the JSON export (test_runner_output.spl).
3. DONE 2026-08-26 — runner-emitted `groups` array in the test JSON
   (per-directory passed/failed/skipped/pending + done_pct), same spec file.
4. Sibling repos adopt the same registry format for standardized dashboards.
5. Replace `update_site.sh` with a `.spl` generator once a released `simple`
   binary is consumable in simply's CI, and wire simply's daily job to read
   the `groups`/`total_pending` JSON to flip registry statuses.

## Update 2026-08-26

- `test --json` is native on every seed dispatch lane (`193af515043`,
  `590a2676e8e`); simply's `data/test_results.json` is verbatim output.
- simply gained `doc/plan/completion_criteria.md` (three gates + status
  ladder) and `data/tests.sdn` (id|kind|path test lists).
- Full `test/01_unit` sweep drives a fix campaign; landed so far:
  `b1ded64c8e4` (sha1_x4 tuple annotation + module import), `8d8d11097a0`
  (`expect_not` export, layout/installer imports), `88fe280bb0f` (tmux
  `to_int_or`), `05b134ac502` (`invalid_node_id` fixtures). Recurring defect
  classes: wrong import module path, missing export, bad tuple annotation,
  auto-id-0 DOM fixtures, stale-API specs from the sspec-modernization waves.
- Process state: `.spipe/simply_showcase/state.md`.
