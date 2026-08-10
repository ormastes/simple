# Specs assert against product files that do not exist — negative legs pass vacuously (2026-08-10)

Status: **RED / OPEN**. 835 specs reference 949 distinct product paths that are
absent from the committed tree. Two rename clusters are fixed (see Fixed
below); the remaining ~849 paths are DELETED or NEVER-EXISTED and their specs
are deliberately left RED.

## The shape

A spec reads a product path that is missing. The read returns empty content.
A **negative** leg then passes against that emptiness:

```
val src = read_file("src/compiler/80.driver/driver/incremental.spl")   # gone
expect(src.contains("legacy_cache_key")).to_equal(false)               # VACUOUS PASS
```

This **overturns a rule that several prior streams and their briefs treated as
sound**: "negative / absence assertions cannot be vacuous." They can. Absence
assertions are vacuous exactly when the subject they assert absence *in* is
itself absent. The prior exclusion was wrong and any vacuity census that
carried it under-counted.

Positive legs (`to_contain`, `to_equal(true)`) fail loudly on a missing file,
which is why this shape hid: it only ever manifests on the negative leg, and a
green negative leg looks like a satisfied invariant.

## Detection

`scripts/check/check-spec-missing-path-vacuity.shs` — fail-closed, three
controls in a fatal `--selftest` that runs before every scan (planted missing
path MUST be flagged; an existing path MUST NOT be; a path appearing only in
the spec's own comment MUST NOT be harvested). Verdict line last on stdout;
zero specs examined is `ERROR` exit 2, never a pass. Mutation proof: disabling
path extraction turns the selftest into `ERROR -- nothing was checked` exit 2.

Whole-corpus run: `FAIL -- 19614 specs checked, 2305 missing-path references`.

Full census: `doc/08_tracking/test/spec_missing_path_census_2026-08-10.tsv`
(`<spec>\t<missing path>`, 2004 rows after excluding `bin/release/**` build
outputs).

## Classification

- **RENAMED** — the file moved; the reference is stale. Tractable, fixed below.
- **DELETED** — the capability is gone. The spec asserts about something that
  no longer exists. Left RED: whether the spec or the product is wrong is a
  per-site product decision, not a mechanical edit.
- **NEVER EXISTED** — the spec was written against an **imagined harness**.

### RETRACTION (2026-08-10, Q33): `git log` is NOT a NEVER-EXISTED oracle here

**This repo is a SHALLOW clone.** `.git/shallow` holds 5 grafts; the whole
reachable history is **1876 commits with a floor of 2026-06-30** — roughly six
weeks. An empty `git log <path>` therefore means *"not touched in the last six
weeks"*, **not** *"never existed"*. Every NEVER-EXISTED claim made on empty-`git
log` evidence is unproven.

Concretely **disproved**: `scripts/qemu_rv64_http_test.shs` and
`scripts/qemu_rv32_http_test.shs` were recorded above as NEVER EXISTED. They are
**RENAMED** — they live at `scripts/qemu/qemu_rv{64,32}_http_test.shs` in the
committed tree today. Fixed in `simpleos_riscv_network_gate_spec.spl`.

The workable method is **structural, not historical**: resolve each missing path
against the *current* committed tree (`git ls-tree -r`) by basename and by
prefix-substitution rules, and accept only resolutions whose target is confirmed
present. Do NOT attempt a whole-history harvest (the predecessor's `git log
--all --name-only` exceeded 6.8 GB before abort; ENOSPC has wiped `main` twice
on this host), and do not trust a scoped `git log` either — it is shallow.

### Q33 classification of the 1026 absent paths (fresh scan of origin blobs)

| class | count | method |
|---|---|---|
| RENAMED-CONFIRMED | 43 | target present in committed tree via prefix-substitution family; rewritten |
| RENAMED-CANDIDATE-UNVERIFIED | 72 | exactly one basename match in the tree, but the implied prefix substitution is not a coherent rename family (e.g. `src/` => `test/fixtures/doctest/`); left RED, not guessed |
| UNRESOLVED (DELETED **or** NEVER-EXISTED) | 911 | no basename match anywhere in the committed tree. Shallow history cannot separate the two. Left RED. |

Full table: `doc/08_tracking/test/spec_missing_path_classification_2026-08-10.tsv`.

Note the census file `spec_missing_path_census_2026-08-10.tsv` is now **stale**:
it still lists the `doc/06_spec/test/**` family, which the predecessor's own fix
already eliminated (0 live references remain). It also contains extraction
artifacts (`config/1`, `config/2`, a path with a literal `\n`, prose fragments
such as ``examples/ide/**` contains sample integrations only``). Re-derive before
relying on it.

## Fixed

- `doc/06_spec/test/**` -> `doc/06_spec/**` (the `test/` segment was dropped
  from the generated manual tree). 25/25 references resolve. 3 specs.
- `examples/simple_os/**` -> `examples/09_embedded/simple_os/**` and
  `examples/ide/**` -> `examples/10_tooling/ide/**`. 108 references, 35 files
  including duplicate-tree twins. Only references whose renamed target was
  confirmed present were rewritten; non-resolving ones were left RED rather
  than guessed.

## Left RED (not weakened)

Everything else in the census, including:

- `native_build_cache_plumbing_spec.spl` — the whole
  `src/compiler/80.driver/driver/` directory is gone (DELETED).
- `simpleos_riscv_network_gate_spec.spl` — `scripts/qemu_rv{64,32}_http_test.shs`
  NEVER EXISTED.
- `.spipe_wrapped_entry_qemu_runner_spec.spl`,
  `scripts/check-heavy-work-preflight.shs`.

No spec was weakened, skipped, or softened.

## Fixed by Q33 (2026-08-10)

Rewrites applied **only in file-read position** (`read_text(`, `read_file(`,
`rt_file_read_text(`, `rt_file_exists(`, `file_exists(`) — deliberately **not**
in `to_contain("...")` content-substring position, where the argument asserts
what a product file's *text* says and repointing it would be a product decision,
not a path repair. 18 spec files, 57 lines, both legs of every duplicate
test-tree pair.

- `scripts/<f>` -> `scripts/{check,os,qemu,rtl}/<f>` — 13 paths. Includes the
  retracted qemu pair above. 14 spec files.
- `doc/07_guide/{editor_tui,ide_llm_integration_guide}.md` -> `doc/07_guide/app/`
  and `doc/07_guide/hardware/kv260_rv64gc_fpga_boot.md` ->
  `doc/07_guide/hardware/fpga/`. 4 spec files.

Duplicate-tree note: 7 twins were checked and genuinely diverge — the `01_unit`
leg of the `qemu_runner*` / `vfs_boot_nvme_lease` / `check_riscv_rtl_linux_smoke`
specs does not reference these scripts at all, so a one-leg edit is correct
there and was verified rather than assumed.

## Wholly-obsolete-spec candidates — FLAGGED, NOT DELETED

**202 spec files have >= 2 product-path references and EVERY one is absent.**
These are candidates for being obsolete outright rather than mis-pointed: the
subject they test may no longer exist. Deleting a spec requires owner approval,
so none was touched. List:
`doc/08_tracking/test/spec_wholly_obsolete_candidates_2026-08-10.tsv`.

Heaviest: `test_daemon_session_scheduler_spec.spl` (22/22 refs absent, both
legs), `lint_cache_spec.spl` (18/18), `test_daemon_concurrent_spec.spl` (16/16),
`llm_process_gen_spec.spl` (13/13), `test_daemon_execution_session_spec.spl`
(13/13), `sspec_maintain/rule_coverage_spec.spl` (13/13). The `test_daemon`
cluster in particular reads like a harness that was replaced wholesale.

## Follow-up

1. ~~Label the remaining paths via scoped per-path `git log`~~ — **retracted**,
   the clone is shallow. Structural resolution against the committed tree is the
   only sound method; see the classification table above.
2. Re-run any prior vacuity census that excluded negative/absence assertions —
   its exclusion is disproved. Specifically:
   `scripts/check/census-spec-vacuity.spl` (owned by another stream — do not
   race it), `doc/08_tracking/test/expect_vacuity_gate_full_corpus_census.md`,
   `doc/08_tracking/bug/comment_cheat_spec_census_2026-08-09.md`, and
   `doc/08_tracking/test/spec_vacuity_families_3_4_gate_gap_2026-08-10.md`.
   Expected correction is **upward in every case**: each excluded
   `to_equal(false)` / negated `to_contain` leg whose subject is a missing file
   is a vacuous pass that was scored as a real one. 2242 missing-path references
   across 747 specs bound the size of the miss.
3. Wire `check-spec-missing-path-vacuity.shs` into the gate once the backlog is
   burned down; it FAILs the whole corpus today.
4. Triage the 202 wholly-obsolete candidates: delete-vs-repair is a per-spec
   owner decision.

## Q34 (2026-08-10): 9 of 72 RENAMED-CANDIDATE-UNVERIFIED confirmed and fixed

Manually reviewed all 72 RENAMED-CANDIDATE-UNVERIFIED rows (prefix
substitution alone is not sufficient evidence of a rename family, so each
was checked individually: target existence, usage site, and whether the
literal sits in file-read position). Result:

- **9 confirmed and fixed** (target present in tree, literal in file-read
  position -- `read_file`/`read_text`/`rt_file_read_text`/`file_read`, or a
  path-returning fn feeding `rt_file_exists`): `doc/03_plan/agent_tasks/
  pure_simple_vhdl_riscv_gap_spawn_plan.md`, `doc/03_plan/
  chrome_modern_web_platform_compat_plan.md`, `doc/03_plan/sys_test/
  wpt_subset_migration.md`, `doc/04_architecture/mdsoc_architecture_tobe.md`,
  `doc/04_architecture/simpleos_multiarch_hal.md`, `doc/04_architecture/
  vhdl_support_matrix.md`, `doc/05_design/tensor_dimensions_design.md`,
  `doc/05_design/vscode_rich_editor_tui.md`, `doc/plans/
  riscv_rtl_simpleos_boot.md`. 18 spec files touched (both legs of every
  duplicate-tree pair: `test/system`+`test/03_system`,
  `test/unit`+`test/01_unit`, `test/integration`+`test/02_integration`).
  Two twins (`tensor_dimensions_spec.spl`, `http_baremetal_spec.spl`) had one
  leg already fixed upstream by another stream; confirmed by direct diff
  before editing only the stale leg.
- **1 rejected as file-read**: `doc/08_tracking/test/test_db.sdn` ->
  `examples/10_tooling/obsidian-search/data/db/test_db.sdn` is a real basename
  match but never read anywhere in the referring spec -- left RED, not
  guessed.
- **4 skipped, deliberately not fixed**: `doc/01_research/
  mcp_command_and_response_gap_analysis_2026-02-24.md`, `doc/02_requirements/
  feature/app/mcp_protocol_compliance.md`, `doc/05_design/
  simple_mcp_debug_design.md` all appear only inside a `docs = [...]` list
  asserted via `count_texts`/`has_text` in `mcp_protocol_gap_matrix_spec.spl`
  -- that is a documentation-linkage content assertion, not a file read;
  repointing it is a product decision per the standing rule. `doc/02_requirements/
  feature/security_aop.md` and `doc/06_spec/security_aop_spec.md` appear only
  inside markdown fixture text (`@@ ...`, `**Requirements:**`) that
  `traceability_spec.spl` parses as *sample input*, not real paths it reads --
  same reasoning, left alone.
- **63 still open** (of the original 72): most are basename-only collisions
  with no coherent rename family -- generic filenames (`new.spl`,
  `module.spl`, `dep.spl`, `mod_b.spl`, `g.spl`, `empty.spl`, `init.spl`) or
  cases where multiple distinct source variants resolve to a single target
  (three `multicore_green.spl` path variants -- `gc_async_mut`, `gc_sync_mut`,
  `nogc_sync_mut` -- all basename-match the one file at
  `nogc_async_mut/concurrent/multicore_green.spl`, which is evidence of
  coincidental collision, not three renames). Left RED per the no-guessing
  rule.

Updated: `doc/08_tracking/test/spec_missing_path_classification_2026-08-10.tsv`
(9 rows RENAMED-CANDIDATE-UNVERIFIED -> RENAMED-CONFIRMED; 52
RENAMED-CONFIRMED / 63 RENAMED-CANDIDATE-UNVERIFIED / 911
UNRESOLVED-DELETED-OR-NEVER-EXISTED of 1026 total).

### Census extractor noise (fixed)

`spec_missing_path_census_2026-08-10.tsv` carried two noise rows:
`test/01_unit/app/sspec_maintain/cache_spec.spl` -> `config/1` and
`config/2`. These are not paths -- they are a default-parameter value and a
call-site literal for a `config: text` parameter in that spec's own fixture
code, harvested because the extractor's prefix filter accepts any string
starting with `config/`. Fixed in
`scripts/check/check-spec-missing-path-vacuity.shs`: bare
`<prefix>/<digits>` literals (no extension, single numeric segment) are now
excluded -- no tracked file in this repo matches that shape. Selftest
re-verified green (3 controls unaffected: planted-missing still flagged,
existing-path still silent, comment-only still ignored). Census row count:
2004 -> 2002.

## Q35 (2026-08-10): all 63 remaining RENAMED-CANDIDATE-UNVERIFIED rows resolved

Reviewed each of the 63 rows left open by Q34. For every row, the target
basename match was confirmed present in the committed tree, then judged on
two axes: (a) is the rename family coherent (same file, not a generic
filename collision) -- verified by reading the target's actual content, not
just its path; (b) does the missing-path literal sit in file-read position
(`read_file`/`read_text`/`rt_file_read_text`/`file_read`/`rt_file_exists`/
`file_exists`) in the referring spec, not inside a `to_contain`/`to_equal`
content or algorithm assertion, and not inside a classification/categorizer
fixture where the string is merely an example input that need not resolve
on disk.

**8 confirmed genuine renames, fixed** (4 commits, all pushed):

| before | after | legs |
|---|---|---|
| `src/hardware/fpga_linux/riscv_fpga_linux.spl` | `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl` | `fpga_linux_split_spec.spl` + `rtl_mdsoc_capsule_boundary_spec.spl`, both `test/03_system`+`test/system` legs (4 files) |
| `src/compiler/80.driver/build/layer_check.spl` | `src/compiler/90.tools/coupling/layer_check.spl` | `layer_ci_spec.spl`, `test/01_unit`+`test/unit` legs (2 files) |
| `test/util/game2d_pin_golden_hash.spl` | `test/fixtures/repro/game2d/game2d_pin_golden_hash.spl` | `game2d_golden_spec.spl`, `test/03_system`+`test/system` legs (2 files) |
| `src/app/llm_caret/claude_full/commands/extra-usage/extra-usage-core.spl` | `doc/11_archive/llm_caret_claude_full_hyphen_port/commands/extra-usage/extra-usage-core.spl` | `extra_usage_command_spec.spl` (no twin) |
| `.../extra-usage/extra-usage-noninteractive.spl` | `doc/11_archive/.../extra-usage/extra-usage-noninteractive.spl` | `extra_usage_command_spec.spl` (no twin) |
| `.../extra-usage/extra-usage.spl` | `doc/11_archive/.../extra-usage/extra-usage.spl` | `extra_usage_command_spec.spl` (no twin) |
| `.../commands/sandbox-toggle/sandbox-toggle.spl` | `doc/11_archive/.../commands/sandbox-toggle/sandbox-toggle.spl` | `review_rewind_sandbox_spec.spl` (no twin) |
| `.../ink/log-update.spl` | `doc/11_archive/.../ink/log-update.spl` | `log-update_spec.spl` (no twin) |

Each fix was verified: target content matches the referring spec's own
description (fpga facade module content, `LayerViolation`/
`find_layer_violations` in layer_check.spl, the FNV-1a determinism script
comment in game2d, and the 83-line `sandbox-toggle.spl` matching the
spec's `> 81` line-count assertion). The `src/compiler/80.driver/build/
baremetal.spl` -> `src/compiler/90.tools/verify/baremetal.spl` candidate
was checked the same way and **rejected**: the target is a ported
`verify-baremetal-setup.sh` script, not the `TargetPreset` struct file the
spec describes (`compile_to_llvm_ir_pure` -- 0 matches in the target).

**55 reclassified UNRESOLVED-DELETED-OR-NEVER-EXISTED** (not fixed, not
re-chaseable):

- **Coincidental basename collisions** (target content or context
  unrelated to the referring spec): three `multicore_green.spl` tier
  variants, three `crt0.s` arch variants (all basename-collide the same
  `arm32/boot/crt0.s`), `dep.spl`/`mod_b.spl`/`new.spl`/`module.spl`/
  `empty.spl`/`g.spl`/generic-name fixture paths, `login.spl`,
  `date.spl`, `api_spec.spl` (x2 sites), `hello_spec.spl`,
  `crypto_spec.spl`, `graph_spec.spl`, `tutorial.md` (vendored jj-cli
  docs, unrelated), `persistent.spl`, `alloc.spl`, `init.spl`.
- **Genuine target but never in file-read position** -- literal appears
  only inside a `to_contain`/`to_equal` content assertion, a
  classification/categorizer fixture string (`mock_categorize`,
  `infer_qemu_arch`, `screenshot_dir_for_spec`, `categorize_test_file`,
  etc. -- the string is a synthetic example input to an algorithm, not a
  path the spec reads), or a path-construction/normalization test
  (`llvm_backend.spl`, `F64.spl` -- asserting a naming convention's
  output, not reading the file): the 6 rows already flagged non-fixable
  in Q34 (`mcp_command_and_response_gap_analysis...md`,
  `mcp_protocol_compliance.md`, `security_aop.md`,
  `simple_mcp_debug_design.md`, `security_aop_spec.md`, `test_db.sdn`),
  plus `shb_types.spl`, `check-executable-size-budgets.shs`,
  `repo_hygiene_gate.spl`, `module_tests.rs`, `INDEX.md` (no longer found
  in the referring `.spl` source at all -- only in the generated
  `doc/06_spec/**.md` manual, which is out of scope to edit), the whole
  test-tree "reorg-shaped" family (`arm64_boot_spec.spl`,
  `remote_baremetal_runtime_spec.spl`, `tmux_rest_api_spec.spl`,
  `collections_qemu_spec.spl`, `runtime_error_stack.spl`,
  `riscv32_spec.spl`) -- all used only as example path strings fed to a
  categorizer/dir-resolver function, never read from disk -- and
  `km.spl`, whose spec *deliberately* asserts both the `.com` and
  non-`.com` on-disk spellings are tolerated (not a stale reference at
  all).
- **Extraction artifacts, not real single paths**: 4
  `multicore_green_*` rows whose "missing path" is actually a full shell
  command string (`src/compiler_rust/target/debug/simple test ...`)
  swept up from a `to_contain` assertion, and one
  `profile_report_contract_test.shs; ...; profile_binary_autoselect_test.shs`
  row that is a semicolon-joined multi-path string from a single
  assertion line, not one path.

No spec was weakened, skipped, or had an assertion softened. Every edit
touched only a `read_file`/`read_text`/`rt_file_read_text`/`file_read`/
`rt_file_exists` literal argument.

Updated: `doc/08_tracking/test/spec_missing_path_classification_2026-08-10.tsv`
(60 RENAMED-CONFIRMED / 0 RENAMED-CANDIDATE-UNVERIFIED / 966
UNRESOLVED-DELETED-OR-NEVER-EXISTED of 1026 total).

Commits: `8d8fc6b8bec` (fpga_linux), `3536ae52127` (layer_check.spl),
`2f8750351fb` (game2d_pin_golden_hash.spl), `f725c3c96e2` (llm_caret
archive family), `854b5ce5888` (TSV reclassification).

### Terminal note on the 911 UNRESOLVED bucket

Re-confirmed this bucket is **closed, not partially worked**: every one of
the 911 paths has zero basename match anywhere in the current committed
tree (`git ls-tree -r`), which is the only sound discriminator available in
this shallow clone (see Q33 retraction above). A deep-history harvest was
already attempted and aborted (>6.8 GB before abort, ENOSPC risk on this
host) -- that avenue is a proven dead end, not an unexplored one. Do not
re-open this bucket without a genuinely new method; re-running the existing
structural/historical methods against it will reproduce the same 911.
