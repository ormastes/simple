# Notebook Lanes — Completion Plan (parallel agents), 2026-08-08

**Parent plans:**
- `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` (original — all streams K/P/X/L/H landed)
- `doc/03_plan/agent_tasks/sspec_spipe_notebook_lanes_doc_update_plan_2026-08-08.md` (doc update — all streams S/G/K/D/R landed)

**Purpose:** close the remaining, honestly-enumerated gaps between "core feature
done and verified" and "goal fully complete". Every item below is a REAL open
item found by audit, not busywork. Each stream is independent — launch in
parallel, one agent per stream.

**Ground rules for every agent (copy into each prompt):**
- Do NOT commit or push. Leave work in the working copy.
- Use `SIMPLE_MODULE_LIMIT=4000` for any `bin/simple test` invocation (known
  pre-existing module-count-limit infra issue, unrelated to this feature).
- The deployed `bin/simple` is the Rust seed (known infra state) — results are
  still authoritative for these specs; note the seed banner in evidence.
- NEVER weaken a failing assertion. A correct RED spec stays RED + bug doc
  (`.claude/rules/testing.md`).
- These files are under concurrent multi-session edit pressure. Immediately
  before AND after any test run, `grep -c <your marker string> <file>` to
  confirm your edit survived; if clobbered, re-apply and re-verify.
- Verify with a FRESH test run you executed yourself; paste the final
  `Results:` line (authoritative) in your report.

---

## Stream C1 — CUDA D3 conformance "index 0 length 0" root cause (HIGH)

**Bug:** `doc/08_tracking/bug/cuda_vm_executor_conformance_array_index_out_of_bounds_2026-08-08.md`
(OPEN, not yet root-caused).

**Symptom:** `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl`
example 1 fails with `semantic: array index out of bounds: index is 0 but
length is 0`; example 2 (call-stack-overflow TRAP) passes. Live dual-GPU host.

**Task:**
1. Instrument the D3 vector dispatch path in
   `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` (and the spec's
   `_run_vector` helper) with length-print probes immediately before each
   indexing site (`out_arena`, `records`, header decode, log decode).
2. Run the spec, identify WHICH zero-length collection is indexed. Likely
   candidates: an error path returning `SvmgRunOutcome` with empty
   `out_arena` that a later reader indexes, or `arena_read` failing silently.
3. Fix at the root (fail-closed: an empty arena must produce
   `ok=false` + error text, never be indexed). Convert probes to level-gated
   logs or delete one-off dumps per log-retention policy.
4. Verify: conformance spec 2/2 PASS (or, if a genuinely distinct device
   defect remains, leave RED and UPDATE the bug doc with the pinned
   root cause + file:line).
5. Regression-check the notebook side:
   `test/02_integration/app/tools/notebook/cuda_exec_spec.spl` must stay 4/4.
6. Update the bug doc status/evidence either way.

## Stream C2 — Vulkan dead-code fix verification + bug-doc sync (SMALL)

**State:** `build_svmg_arena_persisting_data` in
`src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl` was corrected 2026-08-08
to absolute-offset copy (`copy_start = max(data_off, prior_data_off)`,
absolute-index copy loop, `k < ARENA_TOTAL_SIZE` DATA half then verbatim
LOG/RECORD half). It currently has ZERO callers (`vulkan_exec.spl` inlines the
splice). A lint run + `vulkan_vm_executor_conformance_spec.spl` re-run were
in flight when this plan was written.

**Task:**
1. Confirm the absolute-offset version is still on disk (clobber check:
   `grep -n "copy_start" src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl`
   — the buggy version uses `copy_len` and `prior_arena[prior_data_off + k]`).
   Re-apply from the bug doc's follow-up section if reverted.
2. Lint the file; run
   `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`
   (must stay 2/2) and
   `test/02_integration/app/tools/notebook/vulkan_exec_spec.spl` (must stay 3/3).
3. Decide + do ONE of: (a) rewire `vulkan_exec.spl`'s `execute_cell` to call
   the now-correct executor helper (mirrors what `cuda_exec.spl` already does —
   preferred, removes duplicate splice logic), or (b) keep the inline splice
   and add a doc comment on the helper naming `vulkan_exec.spl` as the intended
   caller. Option (a) only if the file stays stable under clobber checks;
   otherwise (b).
4. Update the "reverted" paragraph in
   `doc/08_tracking/bug/vulkan_vm_executor_run_source_clobbers_arena_data_each_call_2026-08-08.md`
   — the root-cause fix is now landed, not reverted.

## Stream L1 — Resolve the two INCONCLUSIVE lab specs (MEDIUM)

`test/03_system/tools/jupyter/lab_http_api_spec.spl` and
`test/.../lab_hardening_spec.spl` never completed a single run (5+ attempts,
host-load timeouts). Sibling lab specs pass, but "probably load" is not a
verdict.

**Task:**
1. Check host load first (`uptime`); if load average > ~2x cores, run the
   specs serially with a generous timeout (`timeout 900`), one at a time,
   nothing else running.
2. Get a definitive `Results:` line for each. PASS → done, record evidence.
   FAIL → triage: real defect gets a bug doc + stays RED; infra/timeout gets
   the same treatment as the export_sdoctest bug (see L2 pattern).
3. If a run STILL cannot complete after 3 serial attempts, file a bug doc
   documenting the reproducible non-completion itself (command, timeout,
   load, where it hangs) — an inconclusive that is filed is acceptable; an
   inconclusive that is silent is not.

## Stream L2 — export_sdoctest subprocess-bound RED (SMALL)

**Bug:** `doc/08_tracking/bug/export_sdoctest_spec_subprocess_bound_too_tight_under_host_load_2026-08-08.md`
— spec asserts a 30s subprocess bound; the command takes ~78s under load.

**Task:** the assertion is a PERFORMANCE bound, not a correctness oracle, so
this is the rare case where changing the bound is legitimate — but do it as an
explicit, documented decision, not a quiet weaken:
1. Measure the command 3x on an idle-ish host to get a real baseline.
2. Either (a) raise the bound to baseline x3 with a comment citing the bug
   doc and measured baseline, or (b) if the ~78s is itself a regression vs a
   previously-fast path, keep the spec RED and extend the bug doc with the
   perf-regression evidence instead (per the perf-regression rule in
   CLAUDE.md). Decide from the measurement, not convenience.
3. Verify the spec's final `Results:` line; update the bug doc status.

## Stream D1 — Execute the doc-plan's final link-check gate (MEDIUM)

The 2026-08-08 doc-update plan mandated a final gate that was never run: one
pass over EVERY doc file touched by streams S/G/K/D/R, checking each
referenced path/symbol actually exists. One stale path
(`test/03_system/jupyter/` → `test/03_system/tools/jupyter/`) was already
found and fixed by hand; siblings were never swept.

**Task:**
1. Enumerate touched docs from the doc-update plan's stream lists (S1-S4,
   G1-G4, K2, D1-D2, R1-R2): `.claude/skills/spipe.md`,
   `.claude/skills/lib/spipe_notebook.md`, `.claude/templates/spipe_template.spl`,
   `.claude/agents/spipe/{dev,spec,implement,verify}.md`,
   `doc/07_guide/infra/{sspec_scenario_manual,sspec_antipatterns,testing,test_layout_traceability}.md`,
   `doc/00_llm_process/layer_expert/test_runner/skill.md`,
   `doc/00_llm_process/feature_expert/notebook_lanes/skill.md`,
   `doc/08_tracking/todo/{sspec_maintain_lane_aware_scoring,spipe_docgen_lane_badges}_2026-08-08.md`,
   `doc/01_research/app/tools/notebook_lanes_research.md`,
   `doc/07_guide/app/tools/jupyter.md`,
   `doc/07_guide/app/spipe/scenario_manual_example.md`.
2. For each doc, extract every repo path and code symbol it references;
   verify path exists (`test -e`) and symbol greps to a definition. Report
   and FIX stale ones (smallest correct edit; if a referenced thing was
   never built, flag to coordinator rather than inventing).
3. Output: a short checklist (doc → checked/fixed/N-refs) written to
   `doc/09_report/notebook_lanes_doc_link_check_2026-08-08.md` is NOT wanted
   (no reports in git) — return the checklist as your final agent report
   text only; land only the FIXES.

## Stream V1 — Sync gh (COORDINATOR-GATED — do not delegate blind)

User asked twice for "sync gh and push"; deferred for contested-WC safety.
This stream runs LAST, after C1/C2/L1/L2/D1 land, executed by the
coordinator or a single trusted agent following `.claude/rules/vcs.md` in
full:
1. `sj raw jj git fetch && sj raw jj rebase -d main@origin` FIRST; resolve
   root-first per the conflict-loop protocol.
2. Scope the commit to files THIS session's streams actually authored
   (temp-index / file-subset landing if the WC carries other sessions' piles
   — see memory `reference_land_file_subset_from_pile_wc_via_temp_index`).
3. Run all three pre-push guards from repo root
   (`check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
   `check-tree-size-push.shs`) — verdict line must be `PASS`.
4. Revert-guard: `git diff main@origin..$TIP` must contain no rewinds of
   files this session didn't touch.
5. Push via bookmark flow; on failure use the SSH direct-push fallback;
   verify with `git ls-remote` + `git show --stat` after.

## Explicitly OUT of scope (filed, not forgotten)

- `jit(remote(cuda(...)))` nested notebook cells — filed as a bug/limitation;
  a separate feature effort, not a completion gap of this plan.
- Rebuilding/redeploying the self-hosted `bin/simple` (seed currently
  deployed) — repo-wide infra issue owned outside this feature.

## Done criteria

- C1: conformance spec 2/2 OR root-caused RED with updated bug doc; notebook
  cuda spec still 4/4.
- C2: absolute-offset helper on disk, lint clean, both Vulkan specs green,
  bug doc follow-up corrected.
- L1: definitive Results line (or filed non-completion bug) for both lab specs.
- L2: measured decision + green spec or documented perf-regression RED.
- D1: every touched doc's refs verified; stale refs fixed.
- V1: guards PASS, pushed, `git ls-remote` verified.

## Status update 2026-08-08 (post-completion, post-clobber recovery)

All C1/C2/L1/L2/D1 streams landed and re-verified once; a mass concurrent-
session revert then wiped most of the day's work back to a stale HEAD (this
file included — recreated from source after being deleted outright). Two
verified fixes escaped the wipe by being committed within the same turn they
were reapplied: `c4d52c77dd5` (Vulkan absolute-offset arena copy,
`lab_http_api_spec.spl` infinite-loop typo). Remaining lost work (CUDA
conformance crash+session-lifecycle fix, `notebook_lanes/skill.md` rewrite,
D1's doc-link fixes) is being redone with immediate per-fix commits this
time, specifically to survive the same clobber pattern.
