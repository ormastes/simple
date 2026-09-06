# Caret / agent manager / smux / slang — what is actually not done

Audit date: 2026-08-24. Every number below was produced by running the named
checker or spec in this worktree, not read out of a plan.

**Evidence status: development observation, not acceptance evidence.** Every
verdict here came from the Rust bootstrap seed, the only in-tree binary that
implements a `test` subcommand. The lane's existing TEST_BLOCKED status
(`.spipe/smux_caret_sspec_quality/state.md`) is unchanged by this audit.

## Headline

Four separate plans record acceptance criteria as DONE that the tree does not
support. Three of those were **regressions the state files never noticed**, and
this audit repaired them. The fourth — full Claude CLI parity — is genuinely
unstarted and is the single largest open item in the lane.

| lane | recorded | measured | verdict |
|---|---|---|---|
| llm-caret-claude-cli-full-parity | design-done | 646/1902 target files exist; 504/1902 meet the 80% LOC bar | **not implemented** |
| llm-caret-claude-cli-harden | dev-done | trace checker FAIL: 501/586 symbols traced, 12 stale rows | **regressed — repaired 2026-08-25, now STATUS: PASS at 586/586 and 34/34 files mapped** |
| smux-caret-sspec-quality | all 7 ACs DONE | 3 specs had been re-clobbered to legacy shape | **regressed — repaired here** |
| llm-caret-messaging | implementation | native carriers release-blocked; live Codex stdio blocked | **blocked, correctly recorded** |
| slang-a1-bootstrap | A1 DONE | artifacts exist under post-reorg paths; A2–A8 untouched | **stale paths, not lost work** |

## 1. Full Claude CLI parity — the real "not done"

`sh scripts/check/check-llm-caret-full-parity-implementation.shs` → **FAIL**

```
file_rows=1902
target_files_exist=646          (34%)
target_files_missing=1256
target_loc_ge_80pct_source=504  (26%)
class_rows=124  class_target_files_missing=15
```

**Correction (2026-08-25): those numbers are an UNDERCOUNT, and the "15 missing
classes" below are not missing at all.** The matrices derive each Simple target
path from the TypeScript basename verbatim, keeping hyphens — the matrix asks
for `ink/events/click-event.spl` while the real, already-written port is
`ink/events/click_event.spl`. All 15 "missing" classes exist as faithful ports
(the matrix's own recorded source line numbers match them exactly, e.g.
`log_update.spl:43 LogUpdate`, `:752 VirtualScreen`), and **101 of the 1256
"missing file" rows are the same naming artifact**. The remaining ~1155 are
genuinely unimplemented, so the lane is still overwhelmingly open — but the
checker cannot be driven green by writing code, and no hyphenated shim files
should be created to satisfy it. Fix: snake_case the derived target when
regenerating the matrices. Filed as
`doc/08_tracking/bug/llm_caret_parity_matrix_target_paths_use_hyphens_2026-08-24.md`.

The Ink cluster had zero test coverage; 8 behavioral specs (73 examples, all
green) were added against the existing ports, covering ESC-strip / CSI-u /
application-keypad / SGR-mouse suppression, first-match resolution and DA1
sentinel draining, resize/offscreen full-reset, and cursor-delta bookkeeping.

The plan is exhaustive by design and forbids skipping rows, so this is a
multi-week lane, not a session task. It was deliberately not opened here. The
missing classes cluster in the Ink terminal-UI layer (`ClickEvent`,
`FocusEvent`, `InputEvent`, `KeyboardEvent`, `TerminalEvent`, `LogUpdate`,
`VirtualScreen`, `TerminalQuerier`) — a coherent first sub-lane if one is
picked up.

## 2. The clobber pattern — three specs, two separate incidents

The lane's state file recorded AC-1 as "41 `fn test_*` converted, 0 remain" and
AC-7 as "56 `fn test_*` -> 56 `it`". Both were true when written and false in
the tree:

- `test/03_system/tools/smux_system_spec.spl` — converted at `aa94bed2717`
  (56 examples, 705 lines), reverted by `376031072c5` to the 858-line legacy
  shape. It was RED under the zero-examples gate (`executed=0 dropped=1`) while
  the state file said DONE.
- `test/01_unit/os/smux_spec.spl` and `test/01_unit/os/smux/smux_dashboard_spec.spl`
  — cleaned at `76c0f2f0837` (0 `fn test_*`), re-clobbered by `f13adc2eca5`,
  which re-added all 41 legacy helpers and reduced every oracle to
  `expect(test_x()).to_equal(true)`. `f13adc2eca5` is the same commit CLAUDE.md
  already names for silently reverting the O(n²) test-manifest reindex fix.

Both were restored (commits `7c6d606ae55`, `10707ee59ff`). `origin/main` still
carries the clobbered versions, so these restores are forward progress rather
than a rewind — verified in both directions before landing, per
`.claude/rules/vcs.md`.

`test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`: **10/15 → 15/15**.
The fail-closed guard worked exactly as designed; nothing was watching its
verdict.

## 3. Agent manager — three status lies, now fixed

`src/app/llm_caret/multi_caret_manager.spl` is bounded and coherent, but
reported process state it had not verified:

1. **Leaked children reported as a clean rollback.** A failed launch calls
   `stop_agent_team` and then unconditionally reported `launch_rolled_back`,
   even when `stop_agent_process` returned `process_kill_failed` on a live pid.
2. **Failed teardown reported as `stopped`.** `stop_multi_caret_manager` always
   returned status `stopped`, reason `stop_attempted`, regardless of outcome.
3. **A partly-dead team reported as fully `exited`.** `poll` collapsed the
   runtime's own `partial` status into `exited`, hiding survivors from any
   supervisor and inviting a double-spawn.

Fixed by counting genuinely-leaked children (status `error` **and** pid > 0 — a
pid ≤ 0 was never spawned and is not a leak) and reporting `error` /
`stop_failed` / `degraded` accordingly. New mirrored spec
`test/01_unit/app/llm_caret/multi_caret_manager_spec.spl`: 6 examples, **2 RED
before the fix, 6 GREEN after**, exercising a real `/bin/sleep` child for the
partial-death case. The file previously had no spec at all.

**Still open (deliberately not built):** there is no respawn. `poll` now tells
the truth about a degraded team but nothing acts on it, and the manager does not
retain the original `AgentLaunchRequest`s needed to relaunch a dead member.
Supervision is a design decision, not a bug fix, and is left for a requirement
that asks for it.

## 4. Traceability report is stale

`sh scripts/check/check-llm-caret-claude-cli-trace.shs` → **FAIL**

- 501/586 caret symbols traced (85 missing) — the gate needs ≥80% and the
  checker additionally requires *every* symbol present
- 12 stale rows, all `_production_*` helpers in `tui_io.spl` that no longer exist

Only the 7 rows for `multi_caret_manager.spl` were added here, so this audit did
not grow the debt. The remaining 85 missing and 12 stale rows are pre-existing
and need the lane owner: blanket-regenerating the inventory would launder
untraced work into a green verdict, which is the failure mode this gate exists
to prevent.

## 5. SSpec documentization score

Scorer: `bin/simple run src/app/sspec_maintain/main.spl scan <spec>`.
(Clear `.simple/cache/sspec-maintain` after any scorer or spec edit.)

| spec | before | after |
|---|---|---|
| `test/01_unit/os/smux_spec.spl` | 74 | **91** |
| `test/01_unit/os/smux/smux_dashboard_spec.spl` | 74 | **91** |
| `test/01_unit/app/llm_caret/multi_caret_manager_spec.spl` | 76 (new) | 76 |
| `test/03_system/tools/smux_system_spec.spl` | 49 | 49 |
| `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl` | 49 | 49 |

What moved the two smux specs from 74 to 91: an authored
purpose/audience/workflow/limitations docstring, ordered `step(...)` narration
per scenario, a same-line `# oracle:` rationale for every numeric expected
value, REQ ids bound inside scenario bodies, and lifecycle links pointed at real
files. Dimensions went narrative 80→100, structure 60→100, oracle 70→100, and
the `SSDOC-TRC-003` blocker cleared.

**Update (same day): the generator ceiling was found and fixed — see below.
Both smux specs now score 95, and the manager spec 84.**

**91 was the ceiling, and the ceiling was the generator, not the specs.** Both
files are at 100 on every authored dimension; the remaining 9 points are
`SSDOC-EVD-002` (-15, steps not visible in the manual) and `SSDOC-MNT-008`
(-20, no traceability section) — both charged against specs for what
`documentize.spl` failed to render. Filed as
`doc/08_tracking/bug/sspec_docgen_dumps_source_instead_of_scenario_manual_2026-08-24.md`.

The two system specs sit at 49 and were left alone: raising them means editing
the very spec that gates this lane, which deserves its own reviewed change.

### The generator ceiling, resolved

The 91 ceiling was a **contract mismatch between two tools**, not a missing
feature. The analyzer counted a manual step only for lines beginning `step ` or
`1. `, or containing `data-step=`; the canonical generator emits `- <label>`
bullets, a form deliberately pinned by an existing test that asserts the ordered
`1. ` form must NOT appear. So every fully-stepped manual scored zero visible
steps. The analyzer was corrected to match what the generator emits, and
`documentize.spl` now emits the `## Traceability` section that never existed.

Confirming that surfaced two real rendering defects, both of which this lane's
own authoring had made visible: step labels were truncated at an escaped quote
(`- Create session \`), and the same-line `# oracle:` markers that
`SSDOC-ORA-003` *requires* were folded into the rendered expected value
(``equals `0)  # oracle: index 0 is ...` ``). Both fixed, with three regression
examples that fail before and pass after.

| spec | start | after authoring | after generator fix |
|---|---|---|---|
| `smux_spec.spl` | 74 | 91 | **95** |
| `smux_dashboard_spec.spl` | 74 | 91 | **95** |
| `multi_caret_manager_spec.spl` | 76 | 76 | **84** |

Detail and the two corrected earlier diagnoses:
`doc/08_tracking/bug/sspec_docgen_dumps_source_instead_of_scenario_manual_2026-08-24.md`.

### Authoring trap worth knowing

`SSDOC-ORA-003` accepts `# oracle:` only on the **same line** as the assertion
(`source_facts.spl:319-321`). A marker on the preceding line — the form the
tool's own `improve` output suggests — parses as an ordinary comment and does
nothing. Both specs lost 30 points to this before the markers were moved inline.

## 6. Slang — stale paths, not lost work

`.spipe/slang-a1-bootstrap/state.md` marks all 9 A1 criteria `[x]`, and four
named paths no longer resolve (`doc/05_design/slang/slang_master_plan.md`,
`doc/05_design/nvfs/{slang_requirements,README}.md`,
`doc/05_design/slang/fs_requests/README.md`). These were **relocated** by
`ddcaffbff87` ("reorganize doc/ with MDSOC feature-domain taxonomy", 295 flat
design files → 10 domains), not deleted; nvfs research now lives at
`doc/01_research/os/nvfs/`. The submodule likewise moved to
`examples/07_ml/slang`, not `examples/slang`. The library scaffold
(`src/lib/gc_async_mut/slang/`), the four model-loader specs, and
`src/app/slang_pack/main.spl` are all present.

Not done: phases **A2–A8** — the scaffold holds only `model_executor/`,
`nvfs_client/`, and `slang_status.spl`; `engine/`, `executor/`, `worker/`,
`core/`, `attention/`, `lora/`, and `entrypoints/` were never created.

## 7. Messaging — blocked, and honestly so

`.spipe/llm-caret-messaging/state.md` is the one state file whose record matches
the tree. Native carriers are release-blocked pending a bootstrap redeploy
(three-build cap exhausted), and live Codex App Server stdio control is blocked
with the red spec removed rather than left passing —
`doc/08_tracking/bug/llm_caret_codex_app_server_piped_stdio_2026-08-02.md`.
No repair was attempted here.

## Recommended next actions

1. Land these restores upstream — `origin/main` still carries all three
   clobbered specs.
2. ~~Fix the generator ceiling~~ — **done**; see "The generator ceiling,
   resolved" above. Remaining in that area: `spipe_docgen_scenario_body_spec`
   carries 16 pre-existing failures in the capture/evidence-metadata family,
   untouched.
3. ~~Retire the trace-report debt~~ — **done 2026-08-25**: 85 rows added, 12
   stale removed, 9 unmapped files described; `check-llm-caret-claude-cli-trace.shs`
   now reports `STATUS: PASS`.
4. Pick the Ink terminal-UI sub-lane if full parity is to be started.
5. ~~Add a CI gate~~ — **done 2026-08-25**: `scripts/check/check-sspec-lane-shape.shs`,
   a fail-closed static guard wired into the repo-hygiene ratchet job. Verified
   against the real incident: all three clobbered blobs FAIL with the correct
   reason. The deep executable check stays authoritative; this is the cheap
   always-on half, because the deep one existed all along and nobody ran it.
