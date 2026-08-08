# Lane ORPHAN2 — rescue the mirror-only ("true orphan") specs

**Status: COMPLETE.** No mirror original touched, no file deleted, nothing
committed, nothing under `src/**` touched. 48 spec runs executed (24 specs x 2
paths), plus 3 serial re-runs to resolve one load-induced timeout.

## 0. Headline

**The relocation was already done before this lane started.** All 24 non-junk true
orphans identified by lane TESTDUP now exist in the numbered tree at the exact
mirrored path and are **byte-identical** (`cmp -s`, 24/24 clean). They are
uncommitted working-copy additions created at **2026-07-27 23:18:37** (`git status`
shows them as adds; `git log` has no commit touching them). So this lane's job
reduced to: independently re-derive the orphan set, verify the copies are faithful,
run both sides, and report path dependencies.

## 1. Independent re-derivation (not trusting TESTDUP's list)

Method — content AND name, both directions:
- `num_all.txt` = 16,266 `.spl` under `test/01_unit|02_integration|03_system`
- `mir_all.txt` = 7,682 `.spl` under `test/unit|integration|system`
- md5 of every file in both trees; numbered tree has 11,600 distinct content hashes
  and 14,987 distinct basenames.
- A mirror file is a **true orphan** iff *no* numbered file shares its basename
  **and** *no* numbered file is byte-identical to it.

Result (`build/orphan_rescue/`):

| Class | count |
|---|---:|
| mirror `.spl` with no basename twin in numbered tree | **1** |
| mirror `.spl` with no byte-identical twin in numbered tree | 1,093 |
| mirror `.spl` failing **both** tests (= true orphan) | **1** |

The single remaining true orphan is
`test/integration/app/.simple_result_1784360140542040_app_mcp_intensive_spec.spl`
— a **leaked runner temp file** (hidden dotfile, 529 lines, a runner-transformed
copy of `app_mcp_intensive_spec.spl`, which lives in `test/02_integration/app/`).
It carries no unique coverage and is genuinely deletable. Note it matches the
runner's `_spec.` selector, so it is currently *executed as a duplicate* on every
default run.

TESTDUP's 25 minus this one = the 24 rescued specs, all now present in the numbered
tree. Re-checked per-file: basename hits = 1, content hits = 1, `cmp` clean, for
all 24.

## 2. The 24 rescued specs and their numbered homes

| # | mirror original | numbered home |
|---|---|---|
| 1–16 | `test/unit/compiler/verification/{cache_correctness, deterministic_emission, lean_basic, lean_block_integration, lean_codegen, lean_workflow, memory_capabilities, naming, proof_reference, regeneration, report_rendering, tool_checker, toolchain_detection, unified_attrs, unsupported_construct, verification_diagnostics}_spec.spl` | `test/01_unit/compiler/verification/<same>` |
| 17 | `test/unit/compiler/parser_gap_array_repeat_mut_param_spec.spl` | `test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl` |
| 18–23 | `test/system/coverage/{coverage_build, coverage_check_api, coverage_core, coverage_doc_stats, coverage_runtime_ffi, coverage_test_runner}_spec.spl` | `test/03_system/coverage/<same>` |
| 24 | `test/system/database/server/db_server_tier_spec.spl` | `test/03_system/database/server/db_server_tier_spec.spl` |

Levels are preserved correctly (`unit` → `01_unit`, `system` → `03_system`), so
the LEVELFIX level-detection fix will classify them the same way the mirror did.

Scope note: 17 of the 24 land under `test/01_unit/compiler/**` and 1 under
`test/03_system/database/**`, both **owned by other live lanes** — this lane did
not create or modify those copies, only verified them. The 6
`test/03_system/coverage/**` copies are in this lane's own path set and were
likewise found already present and identical.

## 3. Path-dependency audit (the landmine sweep)

Swept all 24 for the three known move-breakers:

- **`read_file(...)` — ZERO occurrences.** No spec in the set reads a file from
  disk, so the vacuous-green-on-missing-path failure mode cannot apply here. (The
  string `read_file` appears only as a *literal test datum* — an IO-effect name in
  `verification_diagnostics_spec.spl:55`, `unified_attrs_spec.spl:60`,
  `unsupported_construct_spec.spl:43`.)
- **Relative imports (`use ../`, `"./"`) — ZERO occurrences.** All imports are
  `std.*` namespace form, which is location-independent.
- **`# @cover` annotations — 17 distinct targets, all repo-root-relative**, so the
  move does not affect them. 16 of 17 resolve to an existing file. **1 is stale:**
  `coverage_build_spec.spl:1` → `# @cover src/compiler/80.driver/build/coverage.spl 80%`
  — that path does not exist (the real file is `src/compiler/90.tools/coverage.spl`).
  This is **pre-existing in the mirror copy too**, not introduced by the move, so
  it was left as-is and is reported rather than silently fixed.
- Literal `"src/..."`/`"build/..."` strings elsewhere are **test data** (expected
  values fed to pure functions like `check_coverage`, `ProofUnit.create`), not
  filesystem reads. Unaffected by relocation.

**Conclusion: no spec in this set has a real path dependency on its location.**

## 4. Non-asserting shapes spotted (reported, not fixed)

- **`expect(X.?)` dead assertions — 2 sites** (lane VACUOUS's class):
  - `test/unit/compiler/verification/cache_correctness_spec.spl:21` — `expect(result.?).to_equal(true)`
  - `test/system/coverage/coverage_build_spec.spl:139` — `expect(result.?).to_equal(true)`
  Both replicated verbatim into the numbered copies.
- **Matcher chained directly on a user method call** (`recv.m(x).to_equal(y)`, the
  SPECFIX class): **ZERO occurrences.** Every one of the ~131 matcher call sites in
  this set is properly wrapped as `expect(...).to_*(...)`. Verified by grepping for
  `.to_(equal|contain|be_|have_)` lines lacking `expect(` — count 0.

## 5. Verdicts — before (mirror path) vs after (numbered path)

Every spec was executed **twice** — once at its mirror path (BEFORE) and once at
its numbered path (AFTER). Raw logs: `build/orphan_rescue/runs/<spec>.{mirror,num}.log`.

| Spec | BEFORE (mirror path) | AFTER (numbered path) | Verdict change |
|---|---|---|---|
| cache_correctness_spec | 17 total, 15 passed, 2 failed | 17 total, 15 passed, 2 failed | SAME |
| deterministic_emission_spec | 4 total, 4 passed, 0 failed | 4 total, 4 passed, 0 failed | SAME |
| lean_basic_spec | 4 total, 4 passed, 0 failed | 4 total, 4 passed, 0 failed | SAME |
| lean_block_integration_spec | 10 total, 9 passed, 1 failed | 10 total, 9 passed, 1 failed | SAME |
| lean_codegen_spec | 4 total, 3 passed, 1 failed | 4 total, 3 passed, 1 failed | SAME |
| lean_workflow_spec | 1 total, 0 passed, 1 failed **[no examples executed]** | 1 total, 0 passed, 1 failed **[no examples executed]** | SAME |
| memory_capabilities_spec | 6 total, 5 passed, 1 failed | 6 total, 5 passed, 1 failed | SAME |
| naming_spec | 9 total, 9 passed, 0 failed | 9 total, 9 passed, 0 failed | SAME |
| proof_reference_spec | 11 total, 9 passed, 2 failed | 11 total, 9 passed, 2 failed | SAME |
| regeneration_spec | 4 total, 3 passed, 1 failed | 4 total, 3 passed, 1 failed | SAME |
| report_rendering_spec | 18 total, 18 passed, 0 failed | 18 total, 18 passed, 0 failed | SAME |
| tool_checker_spec | 3 total, 3 passed, 0 failed | 3 total, 3 passed, 0 failed | SAME |
| toolchain_detection_spec | 9 total, 5 passed, 4 failed | 9 total, 5 passed, 4 failed | SAME |
| unified_attrs_spec | 5 total, 1 passed, 4 failed | 5 total, 1 passed, 4 failed | SAME |
| unsupported_construct_spec | 15 total, 13 passed, 2 failed | 15 total, 13 passed, 2 failed | SAME |
| verification_diagnostics_spec | 5 total, 4 passed, 1 failed | 5 total, 4 passed, 1 failed | SAME |
| parser_gap_array_repeat_mut_param_spec | 8 total, 8 passed, 0 failed | 8 total, 8 passed, 0 failed | SAME |
| coverage_build_spec | 1 total, 0 passed, 1 failed **[no examples executed]** | 1 total, 0 passed, 1 failed **[no examples executed]** | SAME |
| coverage_check_api_spec | 24 total, 24 passed, 0 failed | 24 total, 24 passed, 0 failed | SAME (see note) |
| coverage_core_spec | 26 total, 26 passed, 0 failed | 26 total, 26 passed, 0 failed | SAME |
| coverage_doc_stats_spec | 25 total, 25 passed, 0 failed | 25 total, 25 passed, 0 failed | SAME |
| coverage_runtime_ffi_spec | 16 total, 16 passed, 0 failed | 16 total, 16 passed, 0 failed | SAME |
| coverage_test_runner_spec | 35 total, 35 passed, 0 failed | 35 total, 35 passed, 0 failed | SAME |
| db_server_tier_spec | **`Process timed out`, exit 255** | **`Process timed out`, exit 255** | SAME |

**24/24 verdicts identical across the move. No hidden path dependency.**

### 5a. The one apparent DIFF, chased down (do not paper over)

`coverage_check_api_spec` first showed mirror = 24/24 green vs numbered =
`exit 255` — i.e. the exact "verdict changed on relocation" signature the brief
warns about. Investigated rather than accepted: the numbered log ends in
`Process timed out`, produced while the host was at **load average ~70** with six
of this lane's runners plus other lanes' work in flight. Re-run **serially** at the
numbered path: **24 total, 24 passed, 0 failed** — identical to the mirror.
Verdict: **load-induced runner timeout, not a path dependency.** Both logs kept —
`coverage_check_api_spec.num.timeout1.log` (the timeout) and
`coverage_check_api_spec.num.log` (the clean re-run).

### 5b. Reds carried into the maintained tree — FLAGGED, not smuggled

11 of the 24 are **not green**, and each is red *identically on both sides*, so the
redness is pre-existing in the mirror and is **not** caused by relocation. Flagging
explicitly, per the brief:

| Spec | failures | note |
|---|---|---|
| unified_attrs_spec | 4 of 5 | worst ratio in the set |
| toolchain_detection_spec | 4 of 9 | |
| cache_correctness_spec | 2 of 17 | also holds a dead `expect(X.?)` at :21 |
| proof_reference_spec | 2 of 11 | |
| unsupported_construct_spec | 2 of 15 | |
| lean_block_integration_spec | 1 of 10 | |
| lean_codegen_spec | 1 of 4 | |
| memory_capabilities_spec | 1 of 6 | |
| regeneration_spec | 1 of 4 | |
| verification_diagnostics_spec | 1 of 5 | |
| **lean_workflow_spec** | — | **`no examples executed`** — the file runs but registers zero examples. Asserts nothing today. |
| **coverage_build_spec** | — | **`no examples executed`** — same; also carries the stale `@cover` from §3 and a dead `expect(X.?)` at :139. |
| **db_server_tier_spec** | — | **`Process timed out` (exit 255) on both paths**, reproduced serially with the machine quiet. Pre-existing hang, not a move artifact. |

The two `no examples executed` specs are effectively **zero-coverage files**: they
were counted among the "live specs a bulk delete would destroy," but they in fact
assert nothing in their current state. That does not make them deletable (the
intent and the bodies are there), but it does mean the "24 live passing specs"
framing overstates the case — the accurate count is **11 fully green, 10 partially
red, 2 vacuous, 1 hanging**.

## 6. What remains before the mirror can retire

Prerequisite ledger (3 items from TESTDUP §5):

1. **Level detection — DISCHARGED** by lane LEVELFIX (`--unit` now selects 10,975
   numbered-tree specs).
2. **True-orphan relocation — DISCHARGED** (this lane): 24/24 present and
   byte-identical in the numbered tree; 1 remaining "orphan" is a deletable leaked
   temp file.
3. **Diverged pairs — STILL OPEN.** 1,093 mirror `.spl` files have no
   byte-identical counterpart anywhere in the numbered tree (TESTDUP's stricter
   >10-line-diff count was 655). By tree: **unit 816, system 183, integration 94.**
   Until each is merged or judged superseded, deleting the mirror still destroys
   real edits. **This is the only remaining blocker.**

Also still open, outside this lane:
- `src/app/doc/gen_spec_docs.spl:108-130` still builds `{test_dir}/system`,
  `/integration`, `/unit` — a live consumer of mirror paths.
- `config/simple.test.sdn:6-8` still declares the mirror dirs (dead keys).

## 7. Which mirror copies become deletable

Once item 3 above is resolved, these 25 mirror files are safe to delete with **zero
coverage loss**, because their content already exists verbatim in the numbered tree
(or is junk):

- the 24 listed in §2 — each byte-identical to its numbered home (verified `cmp`);
- `test/integration/app/.simple_result_1784360140542040_app_mcp_intensive_spec.spl`
  — leaked runner temp, deletable **now**, independent of item 3.

They are **not deleted by this lane** — mirror deletion is a separate decision, per
the lane brief.

## 8. Artifacts

- `build/orphan_rescue/num_all.txt`, `mir_all.txt`, `num_md5.txt`, `mir_md5.txt`,
  `num_base.txt`, `num_md5only.txt` — the re-derivation inputs
- `build/orphan_rescue/true_orphans.txt` — the 1 confirmed remaining true orphan
- `build/orphan_rescue/nobasename.txt`, `nocontent.txt` — the two orphan axes
- `build/orphan_rescue/runs/*.log` — per-spec run logs (`.mirror.log` / `.num.log`)
- `build/orphan_rescue/{run_one.sh,summarize.sh,todo.txt}` — the harness
- `/tmp/orphan2_backup/` — out-of-tree backup of all 24 mirror originals
