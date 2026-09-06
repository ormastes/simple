# Remaining Feature-Implementation Work — Countable Accounting (2026-07-27)

**Method:** read-only. No builds, no test runs, no source edits. Every number below
names the file and the command that produced it. Where a source is stale or
missing, that is stated rather than filled in with an estimate.

**Headline caution:** the two headline numbers most likely to be quoted
(`doc/TODO.md` "528 items" and the bug-doc corpus) are both **structurally
inflated**. Deduplicated, the real actionable counts are roughly one-third to
one-seventh of the raw figures. Details in §1 and §2.

---

## 0. Source-of-truth health check (read this before trusting any number)

| Source | Expected | Actual | Verdict |
|---|---|---|---|
| `doc/02_requirements/feature/feature.md` | auto-generated every test run (`.claude/rules/structure.md`) | **does not exist** (`ls` → No such file) | **MISSING** |
| `doc/02_requirements/feature/pending_feature.md` | auto-generated every test run | **does not exist** | **MISSING** |
| `doc/08_tracking/test/test_db.sdn` | auto-generated every test run | **does not exist** | **MISSING** |
| `doc/08_tracking/test/test_result.md` | auto-generated every test run | exists, header `**Generated:** 2026-05-19 11:58:31`, file mtime `Jul 1 05:05` | **STALE by ~69 days** |
| `doc/08_tracking/todo/todo_db.sdn` | `bin/simple todo-scan` | exists, mtime `Jul 27 22:02` | current |
| `doc/09_report/stage4_campaign_summary_2026-07-27.md` | — | exists, 40,194 bytes, mtime `Jul 27 22:53` | current |

**Finding F0-a — "pending features" has no current source of truth.** Both
`feature.md` and `pending_feature.md` are absent. Per
`.claude/rules/structure.md` these are regenerated on *every* test run; their
absence means the generator has not run to completion in this tree. Consequently
**no implemented/partial/pending classification of features can be derived from
the intended mechanism.** Anything claiming a "pending feature count" today is
reading a source that does not exist.

**Finding F0-b — test outcomes are ~69 days stale.** `test_result.md` reports
120,809 tests / 108,380 passed / 12,328 failed (89.7%) as of **2026-05-19**.
That 12,328 failure figure must **not** be used as a current remaining-work
number. `test_db.sdn`, the machine-readable companion, is missing entirely.

*Commands:* `ls -la doc/02_requirements/feature/feature.md
doc/02_requirements/feature/pending_feature.md`; `head -20
doc/08_tracking/test/test_result.md`; `ls -la doc/08_tracking/test/`.

---

## 1. TODO breakdown

### 1.1 Raw header (as published)

`doc/TODO.md` header states:

| | Total | Open | Blocked | P0 | P1 | P2 | P3 |
|---|---|---|---|---|---|---|---|
| Published | 528 | 528 | 0 | 0 | 7 | 21 | 500 |

Published "By Area": general 500, runtime 7, interpreter 7, quic-server 7,
stdlib 7. **Verified:** the table body contains exactly 528 priority-bearing
rows (`awk -F'|' 'NF>7 && $5 ~ /P[0-3]/' doc/TODO.md | wc -l` → 528). The header
matches the body. The header is internally consistent.

### 1.2 The header is inflated ~3.2x by mirrored source trees

Deduplicating rows by (priority, description text, line number) — i.e. counting
each physical TODO comment once regardless of how many copies of the file the
scanner walked:

*Command:* `awk -F'|' 'NF>7 && $5 ~ /P[0-3]/ {gsub(/ /,"",$5); print $5"\t"$6"\t"$8}' doc/TODO.md | sort -u | cut -f1 | uniq -c`

| Priority | Published rows | **Unique TODOs** | Inflation |
|---|---|---|---|
| P0 | 0 | **0** | — |
| P1 | 7 | **1** | 7.0x |
| P2 | 21 | **3** | 7.0x |
| P3 | 500 | **163** | 3.07x |
| **Total** | **528** | **167** | **3.16x** |

**Cause.** The scan walks several parallel copies of the same library tree. The
198 distinct file paths in the table (`sort -u` on the file column) distribute as:

| Path root | Rows |
|---|---|
| `test/01_unit` | 120 |
| `test/unit` | 99 |
| `test/02_integration` | 56 |
| `test/feature` | 47 |
| `test/integration` | 39 |
| `test/03_system` | 39 |
| `src/std` | 31 |
| `src/lib` | 31 |
| `test/05_perf` | 30 |
| `test/system` | 15 |
| `test/perf` | 12 |
| `src/compiler` | 4 |
| `src/compiler_rust` | 2 |
| `src/app` | 2 |
| `src/os` | 1 |

`src/lib` and `src/std` hold the *same* 31 files; and `test/01_unit/compiler/std/…`,
`test/unit/compiler/std/…`, `test/01_unit/lib/database/lib/…`,
`test/unit/lib/database/lib/…`, `test/feature/lib/lib/…` are further mirrors of
the same library sources. All were confirmed to **exist on disk** (spot-checked
4/4 paths for the single P1 item), so this is real on-disk duplication, not a
stale index. Likewise `test/01_unit` vs `test/unit`, `test/02_integration` vs
`test/integration`, `test/03_system` vs `test/system`, `test/05_perf` vs
`test/perf` are duplicated numbering schemes for the same suites.

**Finding F1-a — `doc/TODO.md`'s 528 should be read as 167.** The dedup ratio is
not uniform (7x for lib-resident TODOs, ~1x for TODOs that live only in one
tree), so the published per-area table is not a usable priority signal.

### 1.3 Every P1 item, verbatim

**There is exactly one unique P1 TODO** (reported 7 times, once per mirror).
Published area: `interpreter`. Verbatim description from `doc/TODO.md`:

> **[TODO]** Simple wraps SFFI `[u8]` returns as `Option::Some([bytes])` at the
> call-site binding even when the wrapper return type says plain `[u8]` and
> unwraps internally. Repro: 17 failing tests in
> `test/03_system/os_crypto_ref_signature_spec.spl` with "method len not found on
> type enum (receiver value: Option::Some(...))". Root cause likely in
> `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs` return
> marshalling or in the type checker's handling of multi-decl externs (see
> `fs.spl` vs `ffi/io.spl` conflict for `rt_file_read_bytes` pattern).
> Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in
> `doc/09_report/crypto_spec_remains_2026-04-16.md`.

Canonical file reference: **`src/lib/nogc_sync_mut/io/signature_sffi.spl:129`**

The 6 duplicate references (same description, same line 129):
`src/std/nogc_sync_mut/io/signature_sffi.spl`,
`test/01_unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl`,
`test/01_unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl`,
`test/unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl`,
`test/unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl`,
`test/feature/lib/lib/nogc_sync_mut/io/signature_sffi.spl`.

### 1.4 Every P2 item, verbatim

**There are exactly three unique P2 TODOs** (each reported 7 times). Grouped by
subsystem:

| # | Subsystem (published area) | Verbatim description | Canonical file reference |
|---|---|---|---|
| P2-1 | `runtime` — GPU / engine2d | "Interpreter loses the `self` binding when a struct" | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:1304` |
| P2-2 | `quic-server` — networking | "wire transport-level send queue" | `src/lib/nogc_async_mut/io/quic/quic_server.spl:288` |
| P2-3 | `stdlib` — HTTP server / TLS | "extract ALPN from handshake state when ALPN is implemented" | `src/lib/nogc_async_mut/http_server/worker.spl:348` |

Each P2 item's 6 duplicates follow the identical mirror pattern
(`src/std/…`, `test/01_unit/compiler/std/…`, `test/01_unit/lib/database/lib/…`,
`test/unit/compiler/std/…`, `test/unit/lib/database/lib/…`,
`test/feature/lib/lib/…`) at the same line number.

Note the published "By Area" table assigns these to `runtime`(7), `quic-server`(7),
`stdlib`(7) — those 21 rows are exactly these 3 items × 7 mirrors.

### 1.5 P3 by area (counts only)

163 unique P3 TODOs. Grouped by canonical location (mirror paths folded back to
`src/lib/…` where the file is a library mirror; genuine test-file TODOs left in
place):

*Command:* `awk -F'|' 'NF>7 && $5 ~ /P3/ …' doc/TODO.md` with mirror-prefix rewrite, then `sort | uniq -c`

| Area | Unique P3 TODOs |
|---|---|
| `test/02_integration` (spec files) | 54 |
| `test/03_system` (spec files) | 33 |
| `test/01_unit` (spec files) | 29 |
| `test/05_perf` (spec files) | 18 |
| `src/lib/nogc_sync_mut` | 11 |
| `src/lib/nogc_async_mut_noalloc` | 5 |
| `src/lib/skia` | 3 |
| `src/compiler_rust` | 2 |
| `src/compiler` | 2 |
| `src/app` | 2 |
| `test/system` | 1 |
| `src/os` | 1 |
| `src/lib/nogc_async_mut` | 1 |
| `src/lib/gc_async_mut` | 1 |
| **Total** | **163** |

**Finding F1-b — only 28 of 163 unique P3 TODOs live in product source.**
135 of 163 (83%) are inside `test/**` spec files. The product-source P3 backlog
(`src/**`) is **28 items**. Known clusters visible in the table body: GPU physics
solver Phase-5 CUDA upload/kernel/readback (5 items,
`src/lib/*/engine/physics/backend_gpu/gpu_solver.spl`), and f32/f64→`[u8]`
serialization placeholders awaiting `rt_f64_to_bytes`
(6 items, `src/lib/*/engine/render/gpu_{lighting3d,mesh3d}.spl`).

---

## 2. Open bugs

### 2.1 Corpus size and the status-marker problem

`doc/08_tracking/bug/` contains **1,439 `.md` files** (`ls -1 *.md | wc -l`).

The prompt's starting point — "56 bug docs have `**Status:** open`" — **does not
verify**. Measured:

- `grep -licE '^\*\*status:\*\* *open *$'` → **51** files whose status is the bare
  word `open`.
- Only **391** of 1,439 files use the `**Status:**` bold-prefix form at all;
  **1,048 do not** (`grep -L '^\*\*Status:\*\*' *.md | wc -l` → 1048).
- Those 1,048 use other spellings: `Status:` plain (113 in a 400-file sample),
  `## Status` heading (77), lowercase `status:` (17), plus one-off
  `- **Status**`, `### Status` variants.
- **623 of 1,439 files (43%) have no parseable status field of any form.**

**Finding F2-a — the bug corpus has no machine-readable status convention.**
The `Status:` value is free text: a single pass over the `**Status:**` form alone
yields **240+ distinct status strings**, including "source fixed / stage 4
qualification pending", "open — worked around at the call site, root cause not
fixed", "cannot-repro-as-documented", "partially resolved 2026-07-17 — two root
causes found and fixed". Any single count of "open bugs" is therefore an
interpretation, not a measurement, and is stated as such below.

### 2.2 Classified counts

Classification rule (applied per file to the first parseable status line, with a
`## Status` heading fallback):
`OPEN` = starts with open/reproduc/root-cause/localized/filed/unconfirmed/fix-in-progress/blocker/blocked/confirmed;
`CLOSED` = starts with fixed/resolved/closed/complete/done/invalid/superseded/stale/cannot/rejected/documented/design/analyzed/verified;
`PARTIAL_PENDING` = contains pending / remains open / not fixed / deferred / workaround / mitigated / partial;
`OTHER` = parseable but unmatched.

| Bucket | Count | % of 1,439 |
|---|---|---|
| **NO_STATUS** (no parseable field) | **623** | 43.3% |
| CLOSED | 311 | 21.6% |
| **OPEN** | **288** | 20.0% |
| **PARTIAL_PENDING** | **131** | 9.1% |
| OTHER | 86 | 6.0% |

**Remaining-work bug count = 288 OPEN + 131 PARTIAL_PENDING = 419**, with **623
unclassifiable** (i.e. the true figure is somewhere in 419–1,042 and cannot be
narrowed without a status-field cleanup). This is the single largest measurement
gap in this report.

### 2.3 Recency split (OPEN + PARTIAL + OTHER only)

Date taken from the `_YYYY-MM-DD` filename suffix. "Recent" = on/after 2026-06-27
(last 30 days).

| Bucket | Recent (≤30d) | Older (>30d) | No date | Total |
|---|---|---|---|---|
| OPEN | 219 | 51 | 18 | 288 |
| PARTIAL_PENDING | 102 | 24 | 5 | 131 |
| OTHER | 57 | 25 | 4 | 86 |
| **Total** | **378** | **100** | **27** | **505** |

Cross-tab with stage-4 dependence (file mentions `stage 4` / `self-hosted
binary` / `self-hosted bootstrap` / `redeploy`):

| | Recent, stage-4-dependent | Recent, independent | Older, stage-4-dep | Older, independent |
|---|---|---|---|---|
| OPEN | **55** | 164 | 5 | 46 |
| PARTIAL_PENDING | **51** | 51 | 6 | 18 |
| OTHER | 16 | 41 | 7 | 18 |

Filename-only alternative view: the open set skews hard to the present —
2026-07: 104, 2026-06: 13, 2026-05: 3, undated: 12 (using the stricter
`**Status:**`-only parse, n=132).

### 2.4 Open bugs by area

Subset: the 109 files whose *first* `Status:`-form line parsed as open (this is a
subset of the 288, because the `## Status` heading fallback is excluded here —
labelled as such, not extrapolated). Area inferred from filename prefix.

| Area | Open bugs (subset n=109) |
|---|---|
| other / uncategorized | 50 |
| UI / GPU / WM / theme / render / font / web | 20 |
| compiler backend (seed, stage, bootstrap, native, cranelift, llvm, mir, jit, codegen) | 13 |
| compiler frontend (interp, parser, lexer, hir, type, lint) | 9 |
| test infrastructure (test, spec, sspec, spipe, runner) | 6 |
| RISC-V (riscv, rv32, rv64) | 6 |
| OS / kernel (simpleos, kernel, uefi, ovmf, nvme) | 5 |

### 2.5 Bugs filed today, 2026-07-27

**66 bug docs carry today's date** in their filename (`ls -1 *2026-07-27* | wc -l`).
Of those, **17 parse as OPEN**:

| # | File | Area |
|---|---|---|
| 1 | `bootstrap_lane_dict_global_uninitialized_alloca_2026-07-27.md` | compiler backend |
| 2 | `lint_coll006_false_positive_integer_accumulator_2026-07-27.md` | lint |
| 3 | `lint_spipe005_rejects_assert_true_family_2026-07-27.md` | lint |
| 4 | `native_entry_closure_common_import_type_loss_2026-07-27.md` | compiler backend |
| 5 | `native_nil_dict_get_phantom_option_rootcause_2026-07-27.md` | compiler backend |
| 6 | `riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md` | RISC-V / evidence |
| 7 | `riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md` | RISC-V / evidence |
| 8 | `rv64_dtb_overlay_not_materialized_in_soc_address_map_2026-07-27.md` | RISC-V |
| 9 | `seed_jit_wide_i64_literal_miscompile_2026-07-27.md` | seed JIT |
| 10 | `seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md` | seed parser |
| 11 | `selfhost_parser_no_explicit_enum_values_2026-07-27.md` | self-hosted parser |
| 12 | `simple_web_textarea_overlay_review_hard_stop_2026-07-27.md` | UI / web |
| 13 | `stage4_focused_subbuild_star_import_unresolved_2026-07-27.md` | **stage 4** |
| 14 | `theme_ipc_k2_review_hard_stop_2026-07-27.md` | UI / theme |
| 15 | `theme_package_transaction_sync_owner_blocker_2026-07-27.md` | UI / theme |
| 16 | `theme_snapshot_catalog_review_hard_stop_2026-07-27.md` | UI / theme |
| 17 | `wm_glass_qemu_evidence_contract_p1_2026-07-27.md` | WM / evidence |

The remaining 49 of today's 66 are closed, partial, or unparseable.

---

## 3. Feature and NFR requirement docs

*Commands:* `ls -1 doc/02_requirements/feature/*.md | wc -l`;
`ls -1 doc/02_requirements/nfr/*.md | wc -l`;
`grep -l -iE '^\*\*(status|state)' …`

| Directory | `.md` files | Files with a `**Status:`/`Status:` line |
|---|---|---|
| `doc/02_requirements/feature/` | **52** (+ `category/` subdir with 9 entries; 53 total dir entries incl. `README.md`) | **11** (6 with `**Status:`, 5 with plain `Status:`) |
| `doc/02_requirements/nfr/` | **134** | **11** |

**Finding F3-a — feature and NFR docs carry NO consistent status marker, so no
implemented/partial/pending classification is reported here.** Only 11 of 52
feature docs (21%) and 11 of 134 NFR docs (8%) contain any status line at all,
and the 11 that do use two different spellings. Per the task constraint, the
classification is **not invented**; only the file count is reported:

- **52 feature requirement docs**
- **134 NFR requirement docs**
- **186 requirement docs total**, of which **164 (88%) are status-silent**

Combined with Finding F0-a (`feature.md` / `pending_feature.md` both missing),
**there is currently no way to state how many features are implemented vs
pending from the requirements layer.** That gap is the finding.

---

## 4. Requirement-to-test traceability — SAMPLE, NOT A CENSUS

**This is a 10-document sample of 52 feature docs (19%). It is an indicator of
traceability health, not a repo-wide measurement. Do not quote the hit rate as a
census.**

Method: for each feature doc, take the first two underscore-delimited name
tokens and search `test/` for a matching `*spec*.spl` and `doc/06_spec/` for any
matching entry.

| # | Feature doc | `test/` spec | `doc/06_spec/` entry | Hit |
|---|---|---|---|---|
| 1 | `browser_wasm_webgpu_infra_options.md` | none | none | ✗ |
| 2 | `cosmos_openssd_production_hal.md` | `test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl` | `doc/06_spec/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.md` | ✓ |
| 3 | `custom_type_iterator_protocol.md` | none | none | ✗ |
| 4 | `engine2d_four_backend_capture.md` | `test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl` | `doc/06_spec/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.md` | ✓ |
| 5 | `gpu_web_db_offload.md` | `test/03_system/lib/web_db_offload/feature/gpu_web_db_offload_spec.spl` | `doc/06_spec/01_unit/lib/nogc_sync_mut/web_db_offload/gpu_web_db_offload_contract_spec.md` | ✓ |
| 6 | `host_gpu_lane.md` | `test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl` | `doc/06_spec/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.md` | ✓ |
| 7 | `llm_caret_gui_backends.md` | `test/system/llm/llm_caret_live_comprehensive_spec.spl` | `doc/06_spec/01_unit/app/llm_caret/` | ✓ |
| 8 | `multicore_green.md` | `test/05_perf/stress/.spipe_matchers_multicore_green_fanout_spec.spl` | `doc/06_spec/05_perf/stress/multicore_green_fanout_spec.md` | ✓ |
| 9 | `nvme_base_spec_commands.md` | `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl` | `doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md` | ✓ |
| 10 | `perf_profile_reporting.md` | none | none | ✗ |

**Sample hit rate: 7 / 10 (70%).** Three misses — `browser_wasm_webgpu_infra_options`,
`custom_type_iterator_protocol`, `perf_profile_reporting` — have no discoverable
spec under either root by name match. Two caveats: (a) a name-token match can
miss a spec filed under a different name, so 70% is a **lower bound**; (b) hit #8
matched a dotfile-prefixed spec (`.spipe_matchers_…`), which may not be collected
by the runner. **Existence of a spec says nothing about whether it passes** —
and §0 establishes that current pass/fail data does not exist.

---

## 5. The stage-4-blocked set

Primary source: **`doc/09_report/stage4_campaign_summary_2026-07-27.md`** (present,
40,194 bytes, written today).

### 5.1 Stage 4 status per that report

> "**Stage 4 still FAILS. No deploy occurred.**" (§1, line 16)

- `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` is still the
  **2026-07-25 Rust seed** (size 145,290,352 — unchanged; mtime touched to
  2026-07-27 22:06 but no self-hosted binary installed).
- Per §1's history archaeology, **Linux x86_64 has never had a green stage-4
  deploy** in this repo's history. The only documented green full-CLI deploy is
  **macOS aarch64** (`5dbe1bc31f3`, 2026-07-25, gate 11/11).
- Today's campaign drove the stage-4 HIR error count
  **47,513 → 11,826 → 5,950 → 4,008 → 2,224 → 1,681 → 1,077** in one tree
  (§2), with zero segfaults and all ~1,752 HIR modules lowering. That is
  progress, not completion.
- §6.1 warns the residual count is itself **~28% inflated by duplicate-alias
  reporting** (~468 of 1,681 lines are the same physical file under
  symlink-derived aliases) — "**every error count in this campaign is inflated by
  an unknown but substantial factor**". So the ~1,077 residual should be read as
  roughly **~775 real** at best, and even that is not firm.

### 5.2 What this blocks

Per `CLAUDE.md`: "**Default tooling = pure-Simple self-hosted binary, not the
Rust seed.** `test`/`lint`/`fmt`/`build`/`run`/MCP/LSP all run on
`bin/release/<triple>/simple` (built via bootstrap)." Because no self-hosted
binary is deployed on Linux x86_64, **all default tooling currently runs on the
seed**, and every result attributed to "the self-hosted toolchain" is
seed-attributed. Bug
`riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md` (filed
today, OPEN) records exactly this contamination for the RISC-V gates.

Countable blocked set, from §2.3's cross-tab:

| Category | Stage-4-dependent count |
|---|---|
| OPEN bugs mentioning stage 4 / self-hosted binary / redeploy | **62** (55 recent + 5 older + 2 undated) |
| PARTIAL_PENDING bugs likewise | **59** (51 recent + 6 older + 2 undated) |
| OTHER-status bugs likewise | 25 |
| **Total bug docs gated on stage 4** | **146** |

Corpus-wide, **255 of 1,439 bug docs (17.7%) mention stage 4** at all
(`grep -ilE 'stage.?4' *.md | wc -l`).

A distinct, very common status string in the corpus is the family
"**source fixed / stage 4 qualification pending**" and its ~20 near-variants
("source fixed / pure-simple qualification pending", "fixed in source; fresh
stage 4 runtime qualification pending", "current source fixed / fresh stage-4
qualification pending", "provider regressions pass / stage 4 integration
pending", …). These are items where **the code is already written** and only the
deploy gate is missing — they convert to closed the moment stage 4 goes green.
They are the bulk of the 131 PARTIAL_PENDING bucket.

Also gated: the four RISC-V gates keep their seed baseline —
`check-riscv-rtl-truth.shs` PASS; `check-riscv-hardware-gates.shs` **13/22**
(expected 21/22); `check-riscv-formal-dual-track.shs` FAIL;
`check-riscv-product-level-evidence.shs` FAIL.

### 5.3 What is NOT blocked

- **All 4 unique P1+P2 TODOs** (§1.3–1.4) are interpreter/runtime/library source
  defects, actionable against the seed today.
- **28 product-source P3 TODOs** (§1.5) — GPU physics Phase 5, f64→bytes
  serialization, etc. — need runtime primitives, not a stage-4 deploy.
- **164 recent + 46 older = 210 OPEN bugs** with no stage-4 mention.
- Regenerating `feature.md` / `pending_feature.md` / `test_db.sdn` (§0) requires
  a completing test run, which per `CLAUDE.md` is *supposed* to run on the
  self-hosted binary — so this one is **arguably** blocked, but a seed-run test
  pass would restore the data. Listed as actionable-with-caveat.

---

## 6. Plan-checkbox measure (independent cross-check)

The most direct available proxy for "feature implementation remaining" is
unchecked checkboxes in the plan tree.

*Command:* `grep -rho '^\s*- \[[ xX]\]' doc/03_plan --include=*.md | tr -d ' ' | sort | uniq -c`

| | Count |
|---|---|
| Checked `- [x]` | **481** |
| **Unchecked `- [ ]`** | **312** |
| Total | 793 |
| **Completion** | **60.7%** |

Unchecked items by plan subdirectory (count of *files* containing unchecked
items): `lib` 8, `app` 5, `os` 3, `infra` 2, `compiler` 2, `agent_tasks` 2,
`sys_test` 1, `runtime` 1, `language` 1, `hardware` 1, plus
`sspec_modernization_plan.md` at top level.

Highest-density remaining plans:

| File | Unchecked |
|---|---|
| `doc/03_plan/infra/perf_umbrella/perf_checklists.md` | 75 |
| `doc/03_plan/app/simpleos/simpleos_nodejs_ai_cli_migration.md` | 44 |
| `doc/03_plan/lib/scilib/ports/scilib_port_blas.md` | 18 |
| `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md` | 16 |
| `doc/03_plan/infra/audit/serial_sigsegv_and_test_hardening.md` | 16 |
| `doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md` | 12 |
| `doc/03_plan/lib/scilib/ports/scilib_port_math_block.md` | 11 |
| `doc/03_plan/lib/scilib/ports/scilib_port_cuda_fortran.md` | 11 |
| `doc/03_plan/agent_tasks/office_cli_tui_ui_access.md` | 11 |
| `doc/03_plan/sys_test/cuda_host_validation_2026-07-11.md` | 10 |
| `doc/03_plan/lib/scilib/ports/scilib_port_lapack.md` | 10 |
| `doc/03_plan/app/editor/editor_markdown_editing_subsystem.md` | 9 |

Caveat: checkbox state is hand-maintained and not regenerated, so staleness in
either direction is possible. Reported as a cross-check, not a primary count.

---

## 7. Bottom line

| Category | Open count | Actionable now | Blocked | Source |
|---|---|---|---|---|
| **TODO — P0** | 0 | 0 | 0 | `doc/TODO.md` header + body |
| **TODO — P1 (unique)** | **1** | **1** | 0 | `doc/TODO.md`, dedup by (prio, desc, line) |
| **TODO — P2 (unique)** | **3** | **3** | 0 | same |
| **TODO — P3 (unique)** | **163** | **163** | 0 | same |
| &nbsp;&nbsp;↳ of which in `src/**` | 28 | 28 | 0 | mirror-folded path grouping |
| &nbsp;&nbsp;↳ of which in `test/**` | 135 | 135 | 0 | same |
| **TODO total (unique)** | **167** | **167** | **0** | *(published as 528; 3.16x mirror inflation)* |
| **Bugs — OPEN** | **288** | 226 | **62** | 1,439 docs, per-file status parse |
| **Bugs — PARTIAL/PENDING** | **131** | 72 | **59** | same |
| **Bugs — OTHER status** | 86 | 61 | 25 | same |
| **Bugs — NO parseable status** | **623** | unknown | unknown | **43% of corpus — unmeasurable** |
| **Bugs actionable subtotal** | **505** | **359** | **146** | OPEN+PARTIAL+OTHER |
| **Feature requirement docs** | 52 | — | — | status-silent; **no classification possible** |
| **NFR requirement docs** | 134 | — | — | status-silent; **no classification possible** |
| **Plan checkboxes unchecked** | **312** | — | — | `doc/03_plan/**` (of 793; 60.7% done) |
| **Stage-4 HIR errors residual** | ~1,077 raw (~775 after 28% dup) | — | **all** | `stage4_campaign_summary_2026-07-27.md` §2, §6.1 |
| **RISC-V hardware gates** | 9 failing of 22 | — | **all** | same, §1 |
| **Test failures** | 12,328 | — | — | **STALE 2026-05-19 — do not quote** |

### Single largest blocked category

**Bugs gated on the stage-4 self-hosted bootstrap: 146 bug docs** (62 OPEN + 59
PARTIAL/PENDING + 25 OTHER), of which the "source fixed / stage-4 qualification
pending" family is the dominant sub-class — code already written, waiting only on
a green deploy. Stage 4 has **never** been green on Linux x86_64
(`stage4_campaign_summary_2026-07-27.md` §1), so this backlog cannot drain
without that milestone.

### Three counts that do not exist and should not be estimated

1. **Pending features** — `feature.md` and `pending_feature.md` are both absent.
2. **Current test pass/fail** — `test_result.md` is 69 days stale; `test_db.sdn` is gone.
3. **True open-bug total** — 623 of 1,439 bug docs (43%) carry no parseable
   status, so the real figure lies in **419–1,042** and cannot be narrowed
   without a status-field convention cleanup.

### Cheapest high-leverage fixes to the accounting itself

1. Collapse mirror paths in `bin/simple todo-scan` — turns 528 back into 167 and
   makes the priority table meaningful.
2. Enforce one `**Status:** <enum>` line in the bug-doc template — converts 623
   unmeasurable docs into countable ones.
3. Land §6.1 of the stage-4 report (duplicate-alias dedup in the focused
   native-build driver) — the report itself calls it "LOW effort, highest
   leverage"; until it lands, every stage-4 error count is untrustworthy.

---

*Generated 2026-07-27. Read-only accounting: no builds run, no tests run, no
source modified. All commands re-runnable from repo root.*
