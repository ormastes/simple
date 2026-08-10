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
