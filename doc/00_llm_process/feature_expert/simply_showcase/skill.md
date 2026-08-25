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

1. Future-impl SSpec tests (declare-now specs reporting `planned`).
2. `simple test --json` status export for the dashboard generator.
3. Runner-emitted feature grouping + done-% so the dashboard is test-produced.
4. Sibling repos adopt the same registry format for standardized dashboards.
5. Replace `update_site.sh` with a `.spl` generator once a released `simple`
   binary is consumable in simply's CI.
