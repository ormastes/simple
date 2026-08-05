# X25519MLKEM768 Acceleration — AC-11 Documentation Sweep (T-11)

- **Campaign slug:** `x25519mlkem768_acceleration`
- **Task:** T-11, `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md` line 442
- **Date:** 2026-08-05
- **Scope:** read-only audit of AC-11. No artifact files were created or edited;
  only this report was written.

> AC-11 (verbatim, `.spipe/x25519mlkem768_acceleration/state.md` line 27):
> *"Research compares applicable free/open implementations and standards;
> requirements, NFRs, architecture, detail design, test plan, agent-task plan,
> guide, generated manuals, and performance report all use the
> `x25519mlkem768_acceleration` slug or an explicit alias."*

## Headline finding

Only **3 of 10** required artifact categories currently exist on disk in this
worktree. The other 7 were drafted at some point — the campaign's own log says
so (`.spipe/x25519mlkem768_acceleration/state.md` line 66: *"design: Drafted
architecture, detail design, system-test plan, agent-task plan, and TLDR
companions..."*) — but the files are **not present in this worktree, not in
`HEAD` (`3c2bbc248ef`), and not in `origin/main`** (verified via `git fetch
origin main` + `git cat-file -e origin/main:<path>`, all "does not exist").

All 7 missing categories' content was found in a **single dangling, unreachable
git commit**: `1c74085cfce1c76bddac03a84c6d5f55cc27a3ae` (authored
2026-08-04T11:36:10+0000, empty commit message subject/body — likely a jj
snapshot). `git merge-base --is-ancestor` confirms it is an ancestor of neither
`origin/main` nor this worktree's `HEAD`, and `git branch/tag --all --contains`
returns nothing — no live ref points at it or through it. This matches the
project's known "shared-WC / jj snapshot gets orphaned" failure mode (see
`reference_recover_clobbered_files_from_jj_snapshot_commits.md` and
`reference_jj_update_stale_switched_lineage_and_deleted_43_files.md` in the
user memory index). **This is a landing gap, not an authoring gap** — the
content was written once and then lost before it reached `main`.

## Per-category checklist

| # | Category | File(s) found (current worktree) | Slug/alias present | AC-11 verdict |
|---|---|---|---|---|
| 1 | Research (compares free/open implementations + standards) | **MISSING** — `doc/01_research/domain/x25519mlkem768_acceleration.md` and `_tldr`, `doc/01_research/local/x25519mlkem768_acceleration.md` and `_tldr` all absent from disk, `HEAD`, and `origin/main`. Content exists only in dangling commit `1c74085c`. | N/A (no file) | **FAIL** |
| 2 | Requirements (feature) | **MISSING** — `doc/02_requirements/feature/x25519mlkem768_acceleration.md` and `_tldr` absent everywhere except dangling commit `1c74085c` (which also has an `_options`/`_options_tldr` pair not in the task's known list). | N/A | **FAIL** |
| 3 | NFRs | **MISSING** — `doc/02_requirements/nfr/x25519mlkem768_acceleration.md` and `_tldr` absent everywhere except dangling commit `1c74085c`. | N/A | **FAIL** |
| 4 | Architecture | **MISSING** as a campaign artifact. `doc/04_architecture/x25519mlkem768_acceleration.md` and `_tldr` exist only in dangling commit `1c74085c`. A *different*, pre-existing doc — `doc/04_architecture/lib/pqc_hybrid_kex_design.md` (dated 2026-05-01, predates the campaign) — discusses `X25519MLKEM768` 11 times but never mentions the `x25519mlkem768_acceleration` slug and covers TLS+SSH design broadly, not the acceleration campaign's scope (SIMD/GPU backends, config matrix, coverage). No explicit alias note ties it to this campaign, so it does not satisfy AC-11 as-is; I did not add one because doing so would misrepresent scope (see "Not fixed" below). | No explicit alias | **FAIL** |
| 5 | Detail design | **PRESENT** — `doc/05_design/lib/x25519mlkem768_remaining_detail_design.md` | Line 3: `**Slug:** \`x25519mlkem768_acceleration\`` | **PASS** |
| 6 | Test plan | **MISSING** — `doc/03_plan/sys_test/x25519mlkem768_acceleration.md` and `_tldr` absent from disk/`HEAD`/`origin/main`; exist only in dangling commit `1c74085c` (which also has 3 sibling sys_test docs: `x25519mlkem768_accelerator_executor_cache.md`, `x25519mlkem768_cache_lifecycle_branch_addendum.md`, `x25519mlkem768_static_branch_coverage.md`). | N/A | **FAIL** |
| 7 | Agent-task plan | **PRESENT** — `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md`. Companion `doc/03_plan/agent_tasks/x25519mlkem768_acceleration.md` (+`_tldr`) named in the task brief is **MISSING** from disk/`HEAD`/`origin/main` (present only in dangling commit `1c74085c`), but is not required since `remaining_tasks.md` alone carries the slug and is the plan currently governing work. | Line 3 of `remaining_tasks.md`: `**Slug:** \`x25519mlkem768_acceleration\`` | **PASS** |
| 8 | Guide | **MISSING** — no file under `doc/07_guide/` mentions `x25519mlkem768` at all (`grep -rl` returned nothing). The dangling commit `1c74085c` has `doc/07_guide/crypto/x25519mlkem768.md`, whose body mentions the exact slug `x25519mlkem768_acceleration` twice, but that file does not exist in this worktree, `HEAD`, or `origin/main`. | N/A | **FAIL** |
| 9 | Generated manuals | **MISSING** — `doc/06_spec/` (the SPipe-generated manual tree, which mirrors `test/`) has **no** `x25519mlkem768` content anywhere; confirmed both by `find`/`grep -rl` across all of `doc/06_spec` and directly: `doc/06_spec/03_system/app/tls/` (the dir that would mirror `test/03_system/app/tls/feature/x25519mlkem768_*.spl`) does not exist at all, even though the source specs it should be generated from do exist (`test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl`, `_coverage_receipt_spec.spl`, `_evidence_runner_contract_spec.spl`, plus ~45 more unit/integration/perf specs under `test/01_unit`, `test/02_integration`, `test/05_perf`). The dangling commit `1c74085c` has ~40 generated manuals mirroring these specs under `doc/06_spec/{01_unit,02_integration,03_system,05_perf}/...`; none are on disk now. Manual generation was never (re-)run after the current source specs landed, or the generated output was lost with the same dangling commit. | N/A | **FAIL** |
| 10 | Performance report | **PRESENT** — `doc/09_report/x25519mlkem768_acceleration_performance_2026-08-05.md` | Line 3: `- **Campaign slug:** \`x25519mlkem768_acceleration\`` | **PASS** |

## Overall AC-11 determination: **FAIL**

3 of 10 required categories are present and correctly carry the slug (detail
design, agent-task plan, performance report). 7 are missing outright: research,
requirements (feature), NFRs, architecture, test plan, guide, generated
manuals. This is worse than "docs written under the wrong name" — the content
was authored and logged as done, then never landed to `main`.

## What I did NOT fix, and why

Per the task's read-only-survey instructions, I only make a trivial edit when
"a real file exists but is one edit away from carrying an explicit alias
note." That condition did not hold for any of the 7 missing categories — there
is no live file to add a note to; the content genuinely does not exist in the
tree. For category 4 (architecture), a related file exists
(`pqc_hybrid_kex_design.md`) but adding an alias note to it would falsely claim
campaign coverage it doesn't have (no SIMD/GPU/config-matrix/coverage content),
so I left it untouched and reported the gap instead.

## Recommended next step (not executed here — out of this task's scope)

Recover `1c74085cfce1c76bddac03a84c6d5f55cc27a3ae` — e.g.
`git show 1c74085cfce1c76bddac03a84c6d5f55cc27a3ae -- <path>` per file, or
`git checkout 1c74085cfce1c76bddac03a84c6d5f55cc27a3ae -- <paths>` — and land
the 7 missing categories through the normal review/landing protocol
(`doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md` §3). Verify each
recovered doc's content is still current (the campaign has moved since
2026-08-04) before landing, and regenerate `doc/06_spec` manuals from the
current `test/` specs rather than trusting the dangling commit's copies
verbatim, since specs may have changed since.

## Reproduction commands

```bash
cd /home/ormastes/dev/pub/simple/.claude/worktrees/x25519-paired-timing
git fetch origin main
git cat-file -e origin/main:doc/01_research/domain/x25519mlkem768_acceleration.md   # fails: NO
git cat-file -e HEAD:doc/01_research/domain/x25519mlkem768_acceleration.md          # fails: NO
git log --all --diff-filter=A --format=%H -- doc/01_research/domain/x25519mlkem768_acceleration.md | head -1
# -> 1c74085cfce1c76bddac03a84c6d5f55cc27a3ae
git merge-base --is-ancestor 1c74085cfce1c76bddac03a84c6d5f55cc27a3ae origin/main; echo $?   # 1 (not an ancestor)
git ls-tree -r --name-only 1c74085cfce1c76bddac03a84c6d5f55cc27a3ae | grep -i x25519mlkem768
```
