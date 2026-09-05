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

## Update 2026-08-26 (wave 2, parallel agents)

- Five agents, one per ~80-file slice (sorted path) of the 401 FAILs seen at
  3,550/8,807, landed `dddd834f996` `c433e5d091d` `6e7b2eb616a` `9c5595b146d`
  `4907ce1da97` `e5a10e3ee78` `f65ae4a5f9c` `d9ca9d78b1d` `2f3f215003b` —
  48 specs green. Lib bugs fixed: jwt/encode + os/crypto/jwt (block-scoped
  `idx3`), date/*, html/entities, composition (`.to_bytes`→`.bytes`),
  search/inverted_index, engine/{rect,color}, skia/{ot_parser_glyf,
  ot_layout_gpos,glyph_cache,font_loader}, text_advanced, regex_match,
  h2_connection imports, dbfs_engine ctor aliases, ndarray.
- Non-mechanical residue (grammar, interpreter, missing SFFI, spec drift):
  `doc/08_tracking/bug/unit_sweep_language_and_interpreter_gaps_2026-08-26.md`.
- Lessons: slice by sorted path so each agent owns coherent directories; make
  agents run specs in the foreground (one stalled waiting on a background
  batch); give each a private scratch dir (two collided on `out3/`).

## Update 2026-08-26 (waves 3-5, sweep completion)

- Wave 3 `676241b1db3` `9db7dbb836d` (16 specs); wave 4 (compiler tree, 19
  specs + clobber restore) `97c30fce71e` `c8f1bf0c2c2` `bfe408434dd`
  `179e18fc740` `45b92648ff8` `4345c8e197b` `8e9ef608092`.
- Wave 5 (~34 specs, four slices): slice0 `7971f2bffbb` `6a02c0f8c4c`
  `745540b000e` `5c219ddf6d2`; slice1 `a41ef500f83` `64f8098101d`
  `11c816c21d9` `06fa37dc08f` `284ce63b0ac`; slice2 `dc58fec5f1b`
  `8da31723373`; slice3 `e5a7528f063` `46bb8524167` `1f3c1225f8b`
  `aa0fbd39bdf`.
- Wave 5 defect classes were mostly *grammar*, not library: multi-line `if`
  conditions the seed parser rejects when a continuation starts with `self`/`_`
  or when body indent equals continuation indent; inline `unsafe(caps): expr`;
  an undiagnosed "expected expression, found Dedent" in three
  `src/os/port/*.spl`; cross-module `fn x_*(self: X)` method resolution;
  HIR→MIR nil internals for multi-fn sources using `and`/`or`. Recorded as
  items 23-30 in `doc/08_tracking/bug/unit_sweep_language_and_interpreter_gaps_2026-08-26.md`.
- **Sweep-runner lesson (cost a whole session's worth of wall clock).**
  `bin/simple test --json <many files>` silently **stops for good** at the
  first spec that hangs — the 8,807-file sweep died at file 1,340
  (`test/01_unit/app/ui/semantic_backend_helpers_spec.spl`) and every later
  file simply never got a verdict. The fix is `--timeout <seconds>`, which
  gives each file its own budget, emits an `UNVERIFIED <path>: TIMEOUT` line,
  and **continues to the next file**. A separate defect — this note previously
  and wrongly blamed it on combining the two flags — is that `--timeout` is
  **irrelevant**: `--no-session-daemon` with two or more positional paths runs
  only the FIRST one and exits 0, which looks like a clean short run rather
  than a broken one. `parse_child_run` in
  `src/app/test_runner_new/test_runner_single.spl` did
  `if not arg.starts_with("-") and path == "": path = arg`, so later paths fell
  through with no branch, no warning, and no effect on the exit code — even
  when a dropped spec genuinely FAILS. The lane's greenwash hardening (timeout,
  signal, zero-executed, truncation) is all per-file, so none of it can fire
  for a path discarded at parse time. Blast radius is contained: every in-tree
  caller passes exactly one path, so no CI or gate green was invalidated; the
  exposure is interactive/agent batching. Record:
  `doc/08_tracking/bug/test_runner_single_lane_drops_extra_paths_2026-08-27.md`;
  PR #66 makes the lane fail closed naming the dropped paths and adds
  `scripts/check/check-test-runner-single-lane-paths.shs`. Resume protocol when a sweep dies: diff the file list against
  `^(PASS|FAIL) ` verdicts, and the first unverdicted file in original order is
  the offender.
