# Feature Implementation Status Audit — 2026-07-27

**Scope:** read-only audit of `doc/02_requirements/feature/` and `doc/02_requirements/nfr/`.
**Method:** derive implementation status from the documents' own content; cross-check a sample against `src/`, `test/`, `doc/06_spec/`.
**No builds or test runs were executed** (machine load constraint). No source was modified.

---

## 0. Headline finding (read this first)

**The requirement documents do not carry implementation status, so they cannot be
made into a source of truth for "how many features remain".** They are
specification documents ("what to build"), not tracking documents ("what is
built"). Concretely:

| Signal the task asked for | What exists in the corpus |
|---|---|
| Acceptance-criteria checkboxes `- [ ]` / `- [x]` | **4 total, in 1 doc of 184** (0 checked, 3 unchecked in that doc; feature corpus). NFR corpus: **0 checkboxes in 133 docs.** |
| `Status:` headers | **32 occurrences across 184 docs** (11 feature, 21 NFR) — and **every one is document-lifecycle state, not implementation state** (see §2). |
| Explicit completion notes | None in a machine-readable form. Prose keywords like "implemented"/"pending" occur but always as requirement text ("the system **shall** be implemented…"), not as claims about current state. |

Therefore the honest bottom line is: **51 feature docs and 133 NFR docs — 184 of
184 — have NO implementation-status signal of their own. All are UNKNOWN from
document content alone.** Any "N features remain" number derived from these docs
would be fabricated.

Two corrections to the premise of the task, both material:

1. **`feature.md` and `pending_feature.md` are not missing — they moved.** They
   live at `doc/08_tracking/feature/feature.md` (16,274 bytes) and
   `doc/08_tracking/feature/pending_feature.md` (52,216 bytes), with older copies
   at `doc/06_spec/feature.md` and `doc/06_spec/pending_feature.md`. The
   `doc/02_requirements/feature/README.md` still documents them as living in
   that directory, so the README is stale, not the generator.
2. **A live-ish tracker does exist:** `doc/08_tracking/feature/feature_db.sdn`
   (123,426 bytes, mtime 2026-07-27 03:41, 137 rows). But it tracks *feature
   requests*, not completion — see §5. It has no `done` status value at all.

---

## 1. Inventory

### 1.1 Directory contents (source: `find doc/02_requirements/{feature,nfr} -type f`)

| Directory | Files | Breakdown |
|---|---|---|
| `doc/02_requirements/feature/` | 61 | 51 topic docs + `README.md` + `category/` subdir with 9 files |
| `doc/02_requirements/feature/category/` | 9 | `Codegen.md`, `Concurrency.md`, `Control_Flow.md`, `Data_Structures.md`, `Infrastructure.md`, `Language.md`, `Testing_Framework.md`, `Types.md`, `Uncategorized.md` |
| `doc/02_requirements/nfr/` | 134 | 133 topic docs + `README.md`. **No subdirectories** (`find … -type d` returns only the root). |

The task's "52 / 134" counts match `ls doc/02_requirements/feature/*.md` = 52
(51 topic + README) and `ls doc/02_requirements/nfr` = 134 (133 topic + README).
**Working corpus for this audit: 51 feature topic docs + 133 NFR topic docs = 184.**

### 1.2 Feature/NFR pairing (source: stem set intersection)

- Feature stems: 51 · NFR stems: 133
- **Paired (same stem in both dirs): 44**
- Feature-only: 7 · NFR-only: 89
- **Distinct engineering efforts represented: 140**, not 184. Counting feature
  and NFR docs separately double-counts 44 efforts.

### 1.3 Requirement-ID density (source: regex `\b(REQ|NFR|FR)-[A-Z0-9-]+`)

| Corpus | Unique IDs | Docs with 0 IDs |
|---|---|---|
| feature (51) | 430 | 13 |
| nfr (133) | 745 | 36 |
| **total (184)** | **1,175** | **49** |

Prefix frequency across the corpus: `NFR-` 754, `REQ-` 436, `FR-` 22. If you want
a granular denominator for "features remaining", **1,175 requirement IDs** is the
right unit — but none of them has a status field either.

### 1.4 Git dates are not usable as age

`git log --diff-filter=A` reports **all 184 docs added in 2026-07** (51/51 feature,
134/134 NFR). Filesystem mtimes are likewise clustered `2026-07-01 .. 2026-07-27`.
This is consistent with the repo-wide history rewrite / bulk re-add recorded in
project memory. **Neither git dates nor mtimes indicate document age or activity**,
so neither was used as a status proxy.

---

## 2. Marker vocabulary actually found

Source: regex over all 184 docs for `^\s*[-*#>|\s]*\**(status|state|…)\**\s*[:|]`.
**23 distinct marker strings, 32 total occurrences.** The complete observed
vocabulary, with counts:

| Count | Marker text (truncated) |
|---|---|
| 5 | `Status:** Draft` |
| 4 | `Status: selected.` |
| 2 | `Status: selected requirements, recovered.` |
| 2 | `Status:** Selected requirements` |
| 1 each | `Status:** Proposed` · `Status:** Options` · `Status:** Selection required` · `Status:** DRAFT (Research Step 1)` · `Status: Draft` · `Status: Selected NFRs` · `Status:** Selected NFRs` · `Status: selected NFR A on 2026-07-11` · `Status: options only. User selection is required before…` · `Status:** User-selected phased sequence.` · `Status: selected on 2026-07-11 (L2+C1+S1+F1+R1+P1+G1…)` · `Status: **Selected — F1 compiler-first modular integr…` · `Status: **Selected — N3 physical FPGA language qualif…` · `Status: selected requirements, 2026-05-14.` · `Status: option record, 2026-05-14.` · `Status:** requirements / canonical spec (verbatim fr…` · `Status:** In Progress (contract only — no SQLite bui…)` · `Status:** Model (Phase 5 groundwork)` · `Status:** Draft \| In Progress \| Implemented \| Complete…` (a **template legend**, not a value) |

**Interpretation.** The vocabulary is `Draft / Proposed / Options / Selection
required / Selected` — an *authoring* lifecycle describing whether the
requirements themselves have been agreed, not whether code exists. Exactly **one**
doc carries anything resembling an implementation state
(`sqlite_vfs_contract.md`: "In Progress (contract only — no SQLite build)"), and
one more (`Status:** Draft | In Progress | Implemented | Complete`) is a template
legend listing values that are **never actually used anywhere in the corpus**.

That template legend is the smoking gun: the doc model *intends* an
`Implemented / Complete` status, and **zero docs have ever been set to it.**

### 2.1 Section structure (why there are no checkboxes)

Top `##`/`###` headings across the corpus: `Requirements` (26), `Non-Functional
Requirements` (11), `Recommended Selection` (9), `Functional Requirements` (8),
`Performance` (7), `Verification` (7), `Out of Scope` (6), `Reliability` (6),
`Compatibility` (6), `Recommendation` (5), `Targets` (5). `Acceptance` appears
**twice**. These are requirement-specification and option-selection sections. The
docs were never structured to hold per-criterion completion.

---

## 3. Acceptance-criteria checkbox rollup

**This is the section the task expected to be the most objective signal. It is
essentially empty.**

| Corpus | Docs | Docs with ≥1 checkbox | `- [x]` checked | `- [ ]` unchecked | Rollup |
|---|---|---|---|---|---|
| feature | 51 | **1** | **0** | **3** | 0/3 = **0%** on a 1-doc base |
| nfr | 133 | **0** | 0 | 0 | **undefined — no data** |
| **total** | **184** | **1 (0.5%)** | **0** | **3** | **0/3** |

A 0% rollup computed from three checkboxes in one document out of 184 is not a
meaningful measure of anything. **Reported as: insufficient data.**

### 3.1 Where the checkboxes actually are: `.spipe/*/state.md`

The acceptance criteria and phase checklists that the requirement docs lack do
exist — in the SPipe pipeline state files. Source: `find .spipe -name state.md`.

- **378 `state.md` files** across 388 `.spipe/` entries.
- **241** contain an `## Acceptance Criteria` section; **125** contain a
  `## Phase Checklist`.
- **Checkbox rollup: 2,177 checked / 134 unchecked = 2,311 total → 94.2% checked.**

But this number must not be read as "94% of features are done", for two reasons
established in §4:

1. These are **process phase** checkboxes (research done, plan written, spec
   drafted), not acceptance-criteria verdicts. The 241 `AC-n` lines are prose
   bullets, **not** checkboxes — they are never ticked.
2. The pipelines these belong to are mostly stale (§4.1).

---

## 4. SPipe pipeline status — the only per-effort status that exists

Mapping method: normalize doc stem (`[^a-z0-9]` stripped) and match against
`.spipe/` directory names — exact match first, then known suffix strips
(`tldr`, `options`, `hardening`, `production`), then bounded substring match.

| Corpus | Docs | Mapped to a `.spipe` pipeline | exact / suffix / fuzzy | Pipeline CLOSED | Pipeline OPEN | **Unmapped (no pipeline at all)** |
|---|---|---|---|---|---|---|
| feature | 51 | 26 (51%) | 20 / 4 / 2 | **0** | **26** | **25 (49%)** |
| nfr | 133 | 61 (46%) | 43 / 14 / 4 | **26** | 35 | **72 (54%)** |
| **total** | **184** | **87 (47%)** | 63 / 18 / 6 | **26** | **61** | **97 (53%)** |

Corpus-wide `.spipe` totals: **378 pipelines, 171 CLOSED, 207 open, 28 with a
`## Blocked` or `## Blockers` section.**

### 4.1 The CLOSED marker is a stale bulk archive — do not trust it

Source: `grep -rhoE '^#{1,3} (Pipeline )?Status: CLOSED — [0-9-]+' .spipe/*/state.md`

| Closure date | Pipelines closed |
|---|---|
| 2026-05-20 | **157** |
| 2026-05-22 | 1 |
| 2026-05-25 | 1 |
| 2026-06-16 | 1 |
| **total** | **160** (of 171 flagged CLOSED; 11 carry a CLOSED header without a parseable date) |

**157 of 171 closures happened on a single day.** In the 68 days since
2026-05-20, exactly **one** pipeline has been closed — while all 184 requirement
docs in this corpus were being written or revised. The CLOSED flag records a
one-time archival sweep, not ongoing completion tracking. It is the same class of
staleness as the 69-day-old `doc/08_tracking/test/test_result.md` (mtime
2026-07-01, 4,895,113 bytes) noted in the task.

**Consequence:** "0 of 51 feature docs map to a CLOSED pipeline" does **not** mean
zero features are done. It means the feature docs are all newer than the archival
sweep. The marker has no discriminating power.

---

## 5. `feature_db.sdn` — checked, and it does not answer the question

`doc/08_tracking/feature/feature_db.sdn` (mtime **2026-07-27 03:41**, the freshest
tracking artifact in the repo) is a 27-column table with **137 rows** and a
`status` column. Header row: `features |id, group, device, component, title,
description, status, priority, source_file, requirement, research, plan,
architecture, design, system_spec, spec_doc, implementation, unit_tests,
integration_tests, guide, external_system, external_id, external_url,
last_synced_at, created_at, updated_at, valid|`.

| `status` value | Rows |
|---|---|
| `current` | 95 |
| `request` | 41 |
| `blocked` | **1** |
| `done` / `complete` / equivalent | **0 — the value does not occur** |

Priority split: P1 72, P2 44, P0 18, other 3.

**Why it cannot serve as the source of truth:**

1. **No terminal state.** `current` / `request` / `blocked` are intake states. A
   feature that shipped and one that was filed yesterday both read `current`.
2. **Coverage is 6–8%.** Its `requirement` column references only **10 distinct
   `doc/02_requirements/feature/` paths and 10 NFR paths**. That leaves **44 of 52
   feature docs (85%) and 124 of 134 NFR docs (93%) entirely unreferenced.**
3. **Its own traceability columns are mostly empty:** `implementation` non-empty
   in **15/137** rows, `unit_tests` **13/137**, `integration_tests` **13/137**,
   `spec_doc` **18/137**, `system_spec` **18/137**.

Its header comment states it was "Generated from legacy Markdown feature requests
on 2026-06-04" — matching `doc/08_tracking/feature/pending_feature.md`, which is
headed `**Generated:** 2026-06-04` / `**Total Pending:** 116 features`. **That
"116 pending" figure is 53 days stale and predates every doc in this corpus.**

### 5.1 The `category/` tables — the only real `done` marks, and there are 19

`doc/02_requirements/feature/category/*.md` are the surviving fragments of the
auto-generated feature table. They have a `Status` column with an actual
implementation vocabulary (`✅ done`, `🔨 in_progress`). Full tally:

| File | ✅ done | 🔨 in_progress | Total rows |
|---|---|---|---|
| `Codegen.md` | 3 | 2 | 5 |
| `Concurrency.md` | 3 | 0 | 3 |
| `Testing_Framework.md` | 7 | 0 | 7 |
| `Language.md` | 2 | 0 | 2 |
| `Infrastructure.md` | 1 | 0 | 1 |
| `Types.md` | 1 | 0 | 1 |
| `Control_Flow.md` | 0 | 0 | **0 (header only)** |
| `Data_Structures.md` | 0 | 0 | **0 (header only)** |
| `Uncategorized.md` | 0 | 0 | **0 (header only)** |
| **Total** | **17** | **2** | **19** (19 distinct feature IDs) |

Compare: `doc/06_spec/feature.md` records `Last ID: 700.2`, and
`doc/08_tracking/feature/feature.md` records `Last ID:
STATIC_FILE_COMPRESSION_CACHE_INTEGRATION_2026_05_01`. **19 rows survive out of a
feature-ID space that reached ~700.** Three of the nine category files contain a
table header and zero rows. This is a truncated remnant, not a census.

---

## 6. Sample cross-check (n = 12) — LABELLED SAMPLE, NOT A CENSUS

12 docs selected across both corpora and across apparent activity levels. For
each, counted `.spl` files in `src/` and `test/` and `.md` files in `doc/06_spec/`
matching the doc's topic keywords (vendored paths excluded per the Owned-Code
Scope rule).

| # | Corpus | Doc | Keywords | `src/` files | `test/` files | `doc/06_spec/` | Implementation present? |
|---|---|---|---|---|---|---|---|
| 1 | feature | `simple_2d_vector_fonts.md` | vector_font, vector_glyph, glyph_raster | 35 | 34 | 17 | YES |
| 2 | feature | `sound_engine.md` | sound_engine, miniaudio, audio_mixer | 27 | 15 | 3 | YES |
| 3 | feature | `sqlite_vfs_contract.md` | sqlite_vfs, sqlite | 33 | 34 | 10 | YES |
| 4 | feature | `nvme_base_spec_commands.md` | nvme | 80 | 186 | 70 | YES |
| 5 | feature | `multicore_green.md` | multicore, smp_ | 19 | 99 | 62 | YES |
| 6 | feature | `wm_glass_theme_host_simpleos.md` | wm_glass, glass_theme | 7 | 9 | 4 | YES |
| 7 | feature | `riscv32_riscv64_fpga_simpleos_production.md` | rv32_exec_core, rv64_exec_core, vhdl_gen | 60 | 17 | 4 | YES |
| 8 | feature | `update_tuf_trust.md` | tuf, trust_root | 5 | 14 | 4 | YES |
| 9 | nfr | `simple_erp.md` | erp (dir-scoped) | **0** | 0 | 0 | **NO — see note** |
| 10 | nfr | `perf_profile_reporting.md` | perf_profile, profile_report, perf_report | 9 | 6 | 5 | YES |
| 11 | nfr | `sspec_scenario_manual.md` | sspec, scenario_manual | 13 | 39 | 12 | YES |
| 12 | nfr | `host_gpu_lane.md` | host_gpu, gpu_lane | 57 | 82 | 58 | YES |

**Note on #9 (`simple_erp`):** a naive substring search returns 1,520 `src/` hits
because `erp` matches *interp*reter. Re-run with directory scoping
(`find src test -type d -iname '*erp*'`) the only matches are `src/app/interpreter`,
`src/compiler/95.interp`, and interpreter test fixtures. **There is no ERP
implementation in this repo.** Project memory records `simple-erp` as a separate
repository, which is consistent — but it means this NFR doc's subject is not
verifiable from here at all.

### 6.1 Agreement rate — and why the honest number is 0/12

The task asked for "the sample's agreement rate with the doc's claimed status".

**None of the 12 sampled docs makes a status claim.** All 12 are UNKNOWN per §2.
An agreement rate against a claim that does not exist is undefined, and reporting
a percentage here would be fabrication. **Agreement rate: 0/12 (0%) docs had a
status claim available to agree or disagree with.**

What *can* be measured is whether the best available proxy — SPipe pipeline
OPEN/CLOSED — predicts implementation presence:

- All 12 sampled docs map to **OPEN or unmapped** pipelines (0 CLOSED).
- **11 of 12 (92%) nonetheless have substantial implementation in `src/`**, a
  median of 26 files.
- **12 of 12 have test files**; 12 of 12 have `doc/06_spec/` entries (including
  #9, whose hits are the interpreter false-positive — so truthfully 11/12).

**The proxy has zero predictive value: "OPEN" predicted 0/12 implemented, reality
is 11/12 implemented. Proxy accuracy 8%.** Trust in the pipeline markers as a
completion signal should be treated as **nil**.

### 6.2 Corpus-wide artifact presence (same method, all 184 docs)

Keyword-token match of each doc's stem against `find src -name '*.spl'`,
`find test -name '*.spl'`, `find doc/06_spec -name '*.md'`, `find doc/03_plan -name '*.md'`:

| Corpus | Docs | ≥1 `src/` match | ≥1 `test/` match | ≥1 `doc/06_spec/` | ≥1 `doc/03_plan/` |
|---|---|---|---|---|---|
| feature | 51 | 48 (94%) | 49 (96%) | 49 (96%) | 49 (96%) |
| nfr | 133 | 126 (95%) | 128 (96%) | 128 (96%) | 123 (92%) |
| **total** | **184** | **174 (95%)** | **177 (96%)** | **177 (96%)** | **172 (93%)** |

**Caveat, stated plainly:** filename-token matching proves *related code exists*,
not that the requirement is *satisfied*. A doc titled
`simple_web_browser_engine_production_hardening.md` will match dozens of browser
engine files whether the hardening work is 0% or 100% done. This table is an
upper bound on "something was started", **not** a completion measure. It is
reported because it is the only corpus-wide empirical signal available without
running tests.

---

## 7. Blocked-on-stage-4 vs independently actionable

**Finding: the stage-4 pattern does not appear in the requirement corpus. It lives
entirely in the bug tracker.**

| Corpus | Docs | Mention `stage 4` / `stage-4` / `stage4` | Mention `bootstrap` |
|---|---|---|---|
| `doc/02_requirements/feature/` + `nfr/` | 184 | **1** (`nfr/cosmos_openssd_production_hal.md`) | **3** |
| `doc/08_tracking/bug/` | 1,442 | **255 (18%)** | — |

Supporting counts in `doc/08_tracking/bug/` (1,442 `.md` files):

- 255 mention stage 4.
- 131 mention "qualif*" (qualification/qualified).
- **74** match a fixed-but-not-qualified phrasing
  (`(source.{0,20}fixed|fix landed).{0,120}(stage.?4|qualif|pending)`).

The task cited a prior accounting of **146** bug docs in "source fixed / stage-4
qualification pending". This audit's stricter single-regex probe finds **74**
exact-phrasing matches, within a plausible band of 131 "qualification"-mentioning
and 255 stage-4-mentioning bug docs. **The 146 figure is consistent with this
corpus; the discrepancy is regex strictness, not a contradiction.** Either way,
the pattern is confined to bugs.

### 7.1 Blocked-vs-actionable split for the 184 requirement docs

| Category | Count | Basis |
|---|---|---|
| Explicitly blocked on stage-4 bootstrap | **1** | `nfr/cosmos_openssd_production_hal.md` — only doc mentioning stage 4 |
| Mention `blocked`/`blocker` in any sense | **25** (13 feature, 12 NFR) | see list below |
| Mapped to a `.spipe` pipeline with a `## Blocked`/`## Blockers` section | subset of the 28 such pipelines corpus-wide (378 total) | — |
| **No blocking signal → nominally actionable** | **159 of 184 (86%)** | absence of any blocked/blocker/stage-4 token |

The 25 docs containing `blocked`/`blocker` (`grep -rliE '\bblock(ed|er)'`):

`feature/`: `simple_2d_renderdoc_backend_equivalence`, `riscv32_riscv64_fpga_simpleos_production`,
`cosmos_openssd_production_hal`, `sqlite_vfs_contract`, `multicore_green`,
`llm_runtime_vllm_torch_interface`, `llm_runtime_vllm_torch_interface_options`,
`simple_web_browser_engine_production_hardening`, `simpleos_qemu_host_gpu_2d`,
`wm_gui_web_2d_host_env_hardening`, `var_resolution_rules`

`nfr/`: `multicore_green`, `rv64_user_mode_exec`, `simpleos_desktop_core_formal_verification_options`,
`harden_tui_gui_layout_comparison`, `simpleos_ai_cli_js_node_port`,
`wm_gui_web_2d_host_env_hardening`, `sound_engine`, `llm_runtime_vllm_torch_interface_options`,
`simple_web_browser_engine_production_hardening`, `mcpgdb`,
`simpleos_game_compatibility_platform`, `riscv32_riscv64_fpga_simpleos_production`,
`cosmos_openssd_production_hal`, `llm_runtime_vllm_torch_interface`

**Honesty caveat:** these 25 were matched by token, and in these documents
`blocked` is usually *forward-looking scope language* ("shall not be blocked by…",
"if blocked, record a bug") rather than a present-tense status. **The count of
docs actually blocked right now is not determinable from the documents.** The
only defensible statement is: **1 doc names stage 4 as a dependency; 183 do not.**

**Conclusion for §5 of the task:** feature docs do **not** exhibit the "source
fixed / stage-4 qualification pending" pattern found in the bug corpus. Stage-4
bootstrap is a *bug-qualification* bottleneck, not a *feature-delivery* one, as
recorded in these documents.

---

## 8. Bottom line

### 8.1 Counts

| | Feature | NFR | Total |
|---|---|---|---|
| Docs in corpus | **51** | **133** | **184** |
| (plus `README.md`) | 1 | 1 | 2 |
| (plus `category/` tables) | 9 | 0 | 9 |
| **DONE** — doc asserts completion | **0** | **0** | **0** |
| **PARTIAL** — doc asserts partial progress | **1** (`sqlite_vfs_contract.md`, "In Progress (contract only)") | **0** | **1** |
| **PENDING** — doc asserts not-started | **0** | **0** | **0** |
| **UNKNOWN** — no implementation-status signal | **50** | **133** | **183** |

**Answer to "how many features remain to implement": not determinable from these
documents. 183 of 184 (99.5%) carry no status.** The one exception reports
partial progress.

Deduplicated by engineering effort (§1.2): **140 distinct efforts**, of which
**139 are UNKNOWN** and 1 is PARTIAL.

### 8.2 Best available upper/lower bounds (each with its own caveat)

| Bound | Value | Source | Caveat |
|---|---|---|---|
| Features with an explicit `✅ done` mark anywhere in the corpus | **17** | `category/*.md`, §5.1 | Remnant of a table whose ID space reached ~700; 3 of 9 category files are empty |
| Features explicitly `🔨 in_progress` | **2** | `category/Codegen.md` | same |
| Features listed pending by the last generator run | **116** | `doc/08_tracking/feature/pending_feature.md`, `**Generated:** 2026-06-04` | **53 days stale**; predates all 184 docs in this corpus |
| Feature-request rows with no terminal state | **137** (95 current, 41 request, 1 blocked) | `feature_db.sdn`, mtime 2026-07-27 | No `done` value exists in the schema; covers only 6–8% of this corpus |
| Requirement IDs with no status field | **1,175** | §1.3 | The granular denominator, entirely unstatused |
| Docs with related code in `src/` | **174 / 184 (95%)** | §6.2 | Proves work *started*, not *finished* |
| SPipe pipelines still open | **207 / 378** | §4 | 157 of the 171 closures are one bulk sweep on 2026-05-20 |

**These bounds do not reconcile with each other, and that is the finding.** 17
done-marked vs 116 pending vs 137 unterminated requests vs 1,175 unstatused IDs
are four incompatible views produced by four generators that stopped running at
four different times.

### 8.3 No source of truth — explicit statement

**There is currently no source of truth for feature completion in this repository
for 183 of 184 requirement documents.** The four candidate trackers each fail:

| Candidate | Location | Why it fails |
|---|---|---|
| `feature.md` / `pending_feature.md` | `doc/08_tracking/feature/` (moved from `02_requirements/feature/`) | Last generated 2026-06-04 — 53 days stale |
| `test_result.md` | `doc/08_tracking/test/` | mtime 2026-07-01, 69 days stale as noted in the task |
| `feature_db.sdn` | `doc/08_tracking/feature/` | Fresh (2026-07-27) but has **no `done` status value** and covers 6–8% of the corpus |
| `.spipe/*/state.md` | 378 files | CLOSED flag is a single-day bulk archive (157/171 on 2026-05-20); 1 closure in 68 days |

### 8.4 Recommended remediation (not performed — read-only audit)

1. Fix `doc/02_requirements/feature/README.md`, which still points at
   `feature.md` / `pending_feature.md` in a directory that no longer holds them.
2. Add the `Status: Draft | In Progress | Implemented | Complete` field — already
   present as a **template legend** in the corpus and used by **zero** docs — as a
   required front-matter field, and backfill it.
3. Add a terminal `done` state to the `feature_db.sdn` schema; today a shipped
   feature and a fresh request are indistinguishable.
4. Re-run the test-suite generator so `feature.md` / `pending_feature.md` /
   `test_result.md` regain currency. **Deliberately not run here** — the machine
   is at load ~60 and the task forbade builds and test runs.
5. Populate `feature_db.sdn`'s `requirement` column for the 44 feature and 124 NFR
   docs it does not reference, so the 6–8% coverage becomes a real index.

---

## Appendix A — Full inventory table

Columns `src` / `test` / `06_spec` / `plan` show *matched keyword tokens / total
keyword tokens* derived from the filename. They indicate topical presence of
artifacts, **not** completion (see §6.2 caveat). `Doc-stated impl status` is
UNKNOWN for every row except `sqlite_vfs_contract.md`, per §2.

### A.1 `doc/02_requirements/feature/` — 51 topic docs

| # | Doc | Lines | REQ/NFR/FR IDs | SPipe pipeline | src match | test match | 06_spec match | plan match | Doc-stated impl status |
|---|-----|-------|----------------|----------------|-----------|------------|---------------|------------|------------------------|
| 1 | `browser_wasm_webgpu_infra_options.md` | 25 | 0 | OPEN browser-wasm-webgpu-infra | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 2 | `cosmos_openssd_production_hal.md` | 99 | 12 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 3 | `custom_type_iterator_protocol.md` | 39 | 0 | — (none) | 4/4 | 3/4 | 3/4 | 3/4 | UNKNOWN |
| 4 | `engine2d_four_backend_capture.md` | 38 | 6 | — (none) | 3/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 5 | `gpu_web_db_offload.md` | 32 | 20 | OPEN gpu_web_db_offload | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 6 | `host_gpu_lane.md` | 33 | 5 | — (none) | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 7 | `llm_caret_claude_cli_full_parity.md` | 26 | 7 | OPEN llm-caret-claude-cli-full-parity | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 8 | `llm_caret_claude_cli_harden.md` | 33 | 9 | OPEN llm-caret-claude-cli-harden | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 9 | `llm_caret_gui_backends.md` | 18 | 7 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 10 | `llm_runtime_vllm_torch_interface.md` | 67 | 15 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 11 | `llm_runtime_vllm_torch_interface_options.md` | 92 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 12 | `llm_tool_runtime_hardening.md` | 84 | 4 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 13 | `llm_tooling_context_ponytail_mimic.md` | 66 | 18 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 14 | `llm_tooling_context_ponytail_mimic_options.md` | 75 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 15 | `low_dependency_ui_dynsmf.md` | 95 | 10 | OPEN low-dependency-ui-dynsmf | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 16 | `low_dependency_ui_dynsmf_tldr.md` | 21 | 0 | OPEN low-dependency-ui-dynsmf | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 17 | `multicore_green.md` | 104 | 10 | OPEN multicore_green | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 18 | `nvme_base_spec_commands.md` | 12 | 5 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 19 | `office_cli_tui_ui_access.md` | 101 | 12 | OPEN office_cli_tui_ui_access | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 20 | `perf_profile_reporting.md` | 15 | 7 | — (none) | 3/3 | 2/3 | 2/3 | 3/3 | UNKNOWN |
| 21 | `production_gui_web_renderer_parity_hardening.md` | 15 | 2 | OPEN gui_web_renderer_parity_hardening | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 22 | `pure_simple_cli_completeness.md` | 9 | 5 | — (none) | 0/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 23 | `pure_simple_tool_infra_hardening.md` | 36 | 15 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 24 | `riscv32_riscv64_fpga_simpleos_production.md` | 126 | 10 | OPEN riscv32_riscv64_fpga_simpleos_production | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 25 | `search_const_generic_dimension_2026-06-15.md` | 42 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 26 | `shared_multilingual_gpu_fonts.md` | 107 | 15 | OPEN shared_multilingual_gpu_fonts | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 27 | `showcase_apps.md` | 12 | 7 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 28 | `simple_2d_renderdoc_backend_equivalence.md` | 35 | 21 | OPEN simple-2d-renderdoc-backend-equivalence | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 29 | `simple_2d_vector_fonts.md` | 18 | 10 | OPEN simple-2d-vector-fonts | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 30 | `simple_2d_vector_fonts_tldr.md` | 11 | 0 | OPEN simple-2d-vector-fonts | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 31 | `simple_3d_graph_ir.md` | 22 | 3 | — (none) | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 32 | `simple_erp.md` | 51 | 26 | — (none) | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |
| 33 | `simple_web_browser_engine_production_hardening.md` | 76 | 21 | OPEN simple_web_browser_engine_production_hardening | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 34 | `simple_web_browser_production_hardening.md` | 29 | 14 | OPEN simple_web_browser_production_hardening | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 35 | `simple_wm_host_simpleos_fullscreen.md` | 16 | 8 | OPEN simple-wm-host-simpleos-fullscreen | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 36 | `simpleos_filesystem_toolchain_servers.md` | 20 | 7 | OPEN simpleos_filesystem_toolchain_servers | 3/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 37 | `simpleos_memory_leveling.md` | 73 | 10 | OPEN simpleos-memory-leveling | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 38 | `simpleos_memory_leveling_gpu_nic_dma.md` | 114 | 15 | OPEN memory-leveling-gpu-nic-dma | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 39 | `simpleos_nvfs_submodule_migration.md` | 10 | 6 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 40 | `simpleos_qemu_host_gpu_2d.md` | 56 | 20 | OPEN simpleos-qemu-host-gpu-2d | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 41 | `simpleos_qemu_host_gpu_4k_capacity_options.md` | 53 | 0 | — (none) | 3/3 | 2/3 | 2/3 | 2/3 | UNKNOWN |
| 42 | `sound_engine.md` | 27 | 13 | OPEN sound-engine | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 43 | `sqlite_vfs_contract.md` | 102 | 0 | — (none) | 2/2 | 2/2 | 1/2 | 2/2 | UNKNOWN |
| 44 | `sspec_scenario_manual.md` | 119 | 8 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 45 | `ui_cli_llm_access.md` | 75 | 25 | OPEN ui_cli_llm_access | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 46 | `unified_optimizer_plugin.md` | 102 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 2/3 | UNKNOWN |
| 47 | `update_tuf_trust.md` | 82 | 0 | — (none) | 2/2 | 2/2 | 2/2 | 1/2 | UNKNOWN |
| 48 | `var_resolution_rules.md` | 227 | 0 | — (none) | 2/2 | 2/2 | 2/2 | 1/2 | UNKNOWN |
| 49 | `wm_glass_theme_host_simpleos.md` | 48 | 10 | OPEN wm-glass-theme-host-simpleos | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 50 | `wm_glass_theme_host_simpleos_tldr.md` | 16 | 0 | OPEN wm-glass-theme-host-simpleos | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 51 | `wm_gui_web_2d_host_env_hardening.md` | 53 | 12 | OPEN wm_gui_web_2d_host_env_hardening | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |

### A.2 `doc/02_requirements/nfr/` — 133 topic docs

| # | Doc | Lines | REQ/NFR/FR IDs | SPipe pipeline | src match | test match | 06_spec match | plan match | Doc-stated impl status |
|---|-----|-------|----------------|----------------|-----------|------------|---------------|------------|------------------------|
| 1 | `accelerated_shared_ui_backend_architecture_options.md` | 67 | 0 | — (none) | 2/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 2 | `all_regions.md` | 13 | 6 | CLOSED all-regions | 0/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 3 | `browser_wasm_webgpu_infra_options.md` | 25 | 0 | OPEN browser-wasm-webgpu-infra | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 4 | `chrome_modern_web_platform_compat.md` | 20 | 4 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 5 | `common_compression_framework.md` | 65 | 12 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 6 | `compiler_interpreter_optimization_syntax_sugar_2026-04-29_options.md` | 105 | 0 | — (none) | 5/5 | 5/5 | 5/5 | 4/5 | UNKNOWN |
| 7 | `cosmos_openssd_production_hal.md` | 74 | 13 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 8 | `crash_containment_framework.md` | 39 | 6 | — (none) | 2/3 | 2/3 | 2/3 | 2/3 | UNKNOWN |
| 9 | `custom_primitive_sffi_public_api_options.md` | 55 | 0 | CLOSED custom-primitive-sffi-public-api | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 10 | `dangerous_comment_grammar.md` | 18 | 6 | — (none) | 3/3 | 3/3 | 3/3 | 0/3 | UNKNOWN |
| 11 | `dangerous_comment_grammar_options.md` | 94 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 0/3 | UNKNOWN |
| 12 | `dashboard_crash_containment_framework.md` | 17 | 8 | — (none) | 3/4 | 3/4 | 3/4 | 3/4 | UNKNOWN |
| 13 | `driver_display_acceleration_boundary.md` | 13 | 4 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 14 | `driver_dma_direct_io.md` | 16 | 6 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 15 | `engine2d_four_backend_capture.md` | 14 | 6 | — (none) | 3/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 16 | `engine_2d.md` | 14 | 6 | — (none) | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 17 | `executable_size_reduction.md` | 13 | 8 | CLOSED executable-size-reduction | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 18 | `executable_size_reduction_options.md` | 24 | 0 | CLOSED executable-size-reduction | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 19 | `gpu_web_db_offload.md` | 31 | 20 | OPEN gpu_web_db_offload | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 20 | `graphical_backend_equality.md` | 21 | 6 | OPEN graphical_backend_equality | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 21 | `graphical_backend_equality_options.md` | 65 | 0 | OPEN graphical_backend_equality | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 22 | `graphics_backend_acceleration_options.md` | 54 | 0 | CLOSED graphics-backend-acceleration | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 23 | `gui_color_image_pipeline_8k.md` | 20 | 7 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 24 | `gui_color_image_pipeline_8k_options.md` | 64 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 25 | `gui_lib_mac_qemu_arm64_perf_options.md` | 37 | 0 | OPEN gui-lib-mac-qemu-arm64-perf | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 26 | `harden_tui_gui_layout_comparison.md` | 36 | 10 | OPEN harden_tui_gui_layout_comparison | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 27 | `hardware_driver_safety_and_performance_2026-04-15_options.md` | 48 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 3/4 | UNKNOWN |
| 28 | `host_cpu_runtime_variants.md` | 8 | 4 | CLOSED host-cpu-runtime-variants | 1/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 29 | `host_gpu_lane.md` | 24 | 4 | — (none) | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 30 | `html_css_binary_caching.md` | 16 | 11 | — (none) | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 31 | `html_css_binary_caching_options.md` | 65 | 0 | — (none) | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 32 | `kairos_like_simple_mcp_llm_dashboard.md` | 88 | 15 | — (none) | 1/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 33 | `llm_caret_claude_cli_full_parity.md` | 20 | 5 | OPEN llm-caret-claude-cli-full-parity | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 34 | `llm_caret_claude_cli_harden.md` | 24 | 7 | OPEN llm-caret-claude-cli-harden | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 35 | `llm_caret_gui_backends.md` | 15 | 6 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 36 | `llm_runtime_vllm_torch_interface.md` | 39 | 12 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 37 | `llm_runtime_vllm_torch_interface_options.md` | 74 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 38 | `llm_tool_runtime_hardening.md` | 61 | 5 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 39 | `llm_tooling_context_ponytail_mimic.md` | 25 | 8 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 40 | `llm_tooling_context_ponytail_mimic_options.md` | 37 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 41 | `low_dependency_ui_dynsmf.md` | 45 | 9 | OPEN low-dependency-ui-dynsmf | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 42 | `low_dependency_ui_dynsmf_tldr.md` | 16 | 1 | OPEN low-dependency-ui-dynsmf | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 43 | `mcpgdb.md` | 8 | 0 | — (none) | 1/1 | 1/1 | 1/1 | 0/1 | UNKNOWN |
| 44 | `multicore_green.md` | 71 | 12 | OPEN multicore_green | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 45 | `nvfs_completion.md` | 13 | 3 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 46 | `nvme_base_spec_commands.md` | 7 | 3 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 47 | `office_cli_tui_ui_access.md` | 70 | 10 | OPEN office_cli_tui_ui_access | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 48 | `optimization_plugin_jit_hotspot.md` | 19 | 8 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 49 | `perf_profile_reporting.md` | 12 | 5 | — (none) | 3/3 | 2/3 | 2/3 | 3/3 | UNKNOWN |
| 50 | `portable_simd_fp_modules.md` | 16 | 6 | CLOSED portable-simd-fp-modules | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 51 | `portable_simd_fp_modules_options.md` | 74 | 0 | CLOSED portable-simd-fp-modules | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 52 | `production_gui_web_renderer_parity_hardening.md` | 20 | 7 | OPEN gui_web_renderer_parity_hardening | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 53 | `pure_simple_cli_completeness.md` | 6 | 3 | — (none) | 0/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 54 | `pure_simple_profile_guided_executable_optimization_2026-06-01.md` | 30 | 9 | OPEN pure_simple_profile_guided_executable_optimization_2026-06-01 | 3/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 55 | `pure_simple_tool_infra_hardening.md` | 29 | 12 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 56 | `riscv32_riscv64_fpga_simpleos_production.md` | 110 | 8 | OPEN riscv32_riscv64_fpga_simpleos_production | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 57 | `riscv_fpga_linux.md` | 14 | 7 | CLOSED riscv-fpga-linux-rtl-completion | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 58 | `riscv_linux_rtl_dual_arch_completion.md` | 8 | 5 | CLOSED riscv-linux-rtl-dual-arch-completion | 5/5 | 5/5 | 5/5 | 5/5 | UNKNOWN |
| 59 | `rust_runtime_minimization_options.md` | 77 | 0 | — (none) | 2/3 | 2/3 | 2/3 | 3/3 | UNKNOWN |
| 60 | `rv64_linux_rtl_pipeline.md` | 17 | 4 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 61 | `rv64_user_mode_exec.md` | 23 | 6 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 62 | `rv64gc_cpu.md` | 37 | 5 | — (none) | 1/1 | 1/1 | 1/1 | 0/1 | UNKNOWN |
| 63 | `scheduler_process_isolation.md` | 9 | 5 | CLOSED scheduler-process-isolation | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 64 | `science_math_lib_set.md` | 40 | 23 | CLOSED science-math-lib-set | 2/2 | 2/2 | 1/2 | 2/2 | UNKNOWN |
| 65 | `scv.md` | 24 | 10 | CLOSED riscv-fpga-linux-rtl | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |
| 66 | `scv_options.md` | 56 | 0 | — (none) | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |
| 67 | `security_baseline.md` | 67 | 0 | — (none) | 2/2 | 2/2 | 2/2 | 1/2 | UNKNOWN |
| 68 | `security_convention_first_architecture.md` | 26 | 10 | — (none) | 3/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 69 | `security_convention_first_architecture_options.md` | 27 | 0 | — (none) | 3/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 70 | `sffi_bidirectional_interop.md` | 111 | 8 | — (none) | 2/3 | 3/3 | 3/3 | 2/3 | UNKNOWN |
| 71 | `shared_multilingual_gpu_fonts.md` | 36 | 8 | OPEN shared_multilingual_gpu_fonts | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 72 | `shared_wm_renderer_unification.md` | 40 | 8 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 73 | `showcase_apps.md` | 8 | 5 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 74 | `simd_auto_application.md` | 10 | 5 | CLOSED simd-auto-application | 3/3 | 2/3 | 2/3 | 3/3 | UNKNOWN |
| 75 | `simd_fixed_and_scalable_vectors.md` | 16 | 6 | CLOSED simd-fixed-and-scalable-vectors | 3/4 | 4/4 | 3/4 | 4/4 | UNKNOWN |
| 76 | `simple_2d_renderdoc_backend_equivalence.md` | 29 | 16 | OPEN simple-2d-renderdoc-backend-equivalence | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 77 | `simple_2d_vector_fonts.md` | 15 | 9 | OPEN simple-2d-vector-fonts | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 78 | `simple_2d_vector_fonts_tldr.md` | 12 | 0 | OPEN simple-2d-vector-fonts | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 79 | `simple_3d_graph_ir.md` | 9 | 3 | — (none) | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 80 | `simple_browser_chromium_html_parity.md` | 10 | 5 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 81 | `simple_erp.md` | 9 | 3 | — (none) | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |
| 82 | `simple_lsp_visibility_support.md` | 30 | 10 | — (none) | 2/2 | 2/2 | 2/2 | 0/2 | UNKNOWN |
| 83 | `simple_optimization_architecture_roadmap_2026-06-01_options.md` | 70 | 0 | OPEN simple-optimization-architecture-roadmap-2026-06-01 | 1/3 | 2/3 | 3/3 | 3/3 | UNKNOWN |
| 84 | `simple_theme_system.md` | 15 | 4 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 85 | `simple_tui_dependency_size_2026-05-27_options.md` | 47 | 0 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 86 | `simple_web_browser_engine_production_hardening.md` | 42 | 17 | OPEN simple_web_browser_engine_production_hardening | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 87 | `simple_web_browser_production_hardening.md` | 29 | 12 | OPEN simple_web_browser_production_hardening | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 88 | `simple_wm_host_simpleos_fullscreen.md` | 13 | 8 | OPEN simple-wm-host-simpleos-fullscreen | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 89 | `simple_wm_modernization_options.md` | 37 | 0 | OPEN simple-wm-modernization | 0/1 | 0/1 | 0/1 | 1/1 | UNKNOWN |
| 90 | `simpleos_ai_cli_js_node_port.md` | 28 | 7 | OPEN simpleos-ai-cli-js-node-port | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 91 | `simpleos_desktop_core_formal_verification.md` | 28 | 10 | CLOSED simpleos-desktop-core-formal-verification | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 92 | `simpleos_desktop_core_formal_verification_options.md` | 63 | 0 | CLOSED simpleos-desktop-core-formal-verification | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 93 | `simpleos_filesystem_toolchain_servers.md` | 14 | 5 | OPEN simpleos_filesystem_toolchain_servers | 3/4 | 3/4 | 3/4 | 4/4 | UNKNOWN |
| 94 | `simpleos_game_compatibility_platform.md` | 51 | 5 | CLOSED simpleos-game-compatibility-platform | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 95 | `simpleos_memory_leveling.md` | 65 | 8 | OPEN simpleos-memory-leveling | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 96 | `simpleos_memory_leveling_gpu_nic_dma.md` | 69 | 10 | OPEN memory-leveling-gpu-nic-dma | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 97 | `simpleos_multiplatform_build.md` | 12 | 4 | — (none) | 3/3 | 3/3 | 3/3 | 2/3 | UNKNOWN |
| 98 | `simpleos_nvfs_submodule_migration.md` | 7 | 4 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 99 | `simpleos_qemu_host_gpu_2d.md` | 27 | 13 | OPEN simpleos-qemu-host-gpu-2d | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 100 | `simpleos_qemu_host_gpu_4k_capacity_options.md` | 55 | 0 | — (none) | 3/3 | 2/3 | 2/3 | 2/3 | UNKNOWN |
| 101 | `simpleos_riscv_smf_fs_launch.md` | 7 | 3 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 102 | `simpleos_rv64_hosted_qemu.md` | 7 | 3 | CLOSED simpleos-rv64-hosted-qemu | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 103 | `simpleos_wine_substrate.md` | 33 | 6 | — (none) | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 104 | `sound_engine.md` | 19 | 11 | OPEN sound-engine | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 105 | `spipe_llm_finetune_process.md` | 17 | 0 | — (none) | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 106 | `spipe_process_harness.md` | 10 | 5 | CLOSED spipe-process-harness | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 107 | `spm_claim_rebind.md` | 13 | 4 | — (none) | 1/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 108 | `spm_priv_check_task_mirror.md` | 13 | 4 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 109 | `spm_pt_walk_user_copy.md` | 11 | 4 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 110 | `svim.md` | 30 | 10 | CLOSED svim | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 111 | `svim_options.md` | 24 | 0 | CLOSED svim | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 112 | `t32_terminal_power_remote.md` | 100 | 6 | — (none) | 3/3 | 3/3 | 3/3 | 0/3 | UNKNOWN |
| 113 | `target_instruction_optimization_32bit_options.md` | 34 | 0 | — (none) | 3/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 114 | `tmux_simpleos.md` | 75 | 10 | CLOSED tmux-simpleos | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 115 | `ui_access_protocol.md` | 54 | 14 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 116 | `ui_access_protocol_options.md` | 72 | 0 | — (none) | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 117 | `ui_cli_llm_access.md` | 44 | 22 | OPEN ui_cli_llm_access | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 118 | `ui_render_feature_caret_options.md` | 65 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 119 | `unified_compute_stdlib_parity_verification_draft.md` | 34 | 5 | — (none) | 5/6 | 5/6 | 5/6 | 6/6 | UNKNOWN |
| 120 | `vhdl_backend_linux_rtl_options.md` | 46 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 121 | `vhdl_python_hdl_parity.md` | 12 | 5 | — (none) | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 122 | `vscode_math_editor_panel_options.md` | 66 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 3/4 | UNKNOWN |
| 123 | `vscode_rich_editor_options.md` | 72 | 0 | — (none) | 3/3 | 3/3 | 3/3 | 2/3 | UNKNOWN |
| 124 | `warning_allow_root_cause_cleanup.md` | 21 | 4 | CLOSED warning-allow-root-cause-cleanup | 3/5 | 5/5 | 5/5 | 5/5 | UNKNOWN |
| 125 | `web_db_primitive_hardening.md` | 18 | 5 | CLOSED web-db-primitive-hardening | 1/1 | 1/1 | 1/1 | 1/1 | UNKNOWN |
| 126 | `wm_glass_theme_host_simpleos.md` | 37 | 8 | OPEN wm-glass-theme-host-simpleos | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 127 | `wm_glass_theme_host_simpleos_tldr.md` | 14 | 0 | OPEN wm-glass-theme-host-simpleos | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 128 | `wm_gui_web_2d_host_env_hardening.md` | 41 | 10 | OPEN wm_gui_web_2d_host_env_hardening | 0/0 | 0/0 | 0/0 | 0/0 | UNKNOWN |
| 129 | `wm_text_access_mcp.md` | 38 | 7 | OPEN wm_text_access_mcp | 2/2 | 2/2 | 2/2 | 2/2 | UNKNOWN |
| 130 | `workspace_root_write_guard.md` | 66 | 19 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
| 131 | `world_units_newunit.md` | 11 | 4 | — (none) | 2/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 132 | `x86_64_desktop_driver_completion.md` | 18 | 7 | CLOSED x86-64-desktop-driver-completion | 3/3 | 3/3 | 3/3 | 3/3 | UNKNOWN |
| 133 | `x86_dual_arch_qemu_boot_options.md` | 81 | 0 | — (none) | 4/4 | 4/4 | 4/4 | 4/4 | UNKNOWN |
