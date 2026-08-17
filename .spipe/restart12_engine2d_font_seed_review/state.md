# Feature: restart12-engine2d-font-seed-review

## Raw Request
Engine2D font and compiler-seed structural review; verify pushed changes and
continue one disjoint pure-Simple criterion. Pure-Simple self-hosted evidence
only, never Rust seed test evidence.

## Task Type
review

## Refined Goal
Structurally review the two changes pushed at `f6cadcc36aff` that touch this
lane (`b10f1b4309c` engine2d font offload, `8d96687c991` seed HIR lowering),
verify each acceptance criterion at most once under an admitted pure-Simple
runtime, and close the lane with fail-closed system coverage and knowledge
artifacts. Report blockers rather than looping or substituting seed evidence.

## Base Revision
`f6cadcc36aff61d16d988651ea36a040d2af6aad`

## Acceptance Criteria
- [x] AC-1: `b10f1b4309c` reviewed structurally — the `backend_canonical_name` call site repair is complete (all three sites), the alias table folds into an all-lowercase preference order, and the Vulkan `.initialized` guard is correctly scoped.
- [x] AC-2: The `.initialized` guard's scope is justified against every sibling backend arm — no other arm can diverge `self.backend` from a non-nil sibling field, so no sibling patch is warranted. Source change deliberately NOT made.
- [x] AC-3: `8d96687c991` reviewed structurally — defect found and traced end to end: the builtin-`Option` exception is keyed on `name == "Option"` while both runtimes key on the reserved enum id, making a user-declared `Option`'s `Some` arm irrefutable and its `None` arm unmatchable.
- [x] AC-4: Every unfixed gap has a `doc/08_tracking/bug` record with owner and unblock condition.
- [x] AC-5: Fail-closed step-based SSpec system coverage exists under `test/03_system` with real assertions and REQ traceability, designed to execute when a qualified runtime is admitted.
- [x] AC-6: Knowledge is current — mirrored `doc/06_spec` Markdown manuals (no executable `.spl`), lane test plan, two `doc/07_guide` pages, this state file, and the feature-expert wiki entry.
- [ ] AC-7: **TEST_BLOCKED** — runtime verdict for the engine2d fallback ledger (REQ-E2DFONT-001..003). No qualified pure-Simple runtime exists. **Not PASS. Not claimed.**
- [ ] AC-8: **TEST_BLOCKED** — runtime verdict for user-`Option` lowering (REQ-OPTLOWER-001..003). Same blocker. **Not PASS. Not claimed.**

## Static gate results (run once each, 2026-08-16)

The runtime lane being blocked does not excuse the future-executable SSpec from
static quality. Each gate was run once; all pass.

| Gate | Command | Verdict |
|---|---|---|
| Real assertions / non-vacuous | `check-vacuous-specs.shs --root <both specs>` | PASS — 2 files scanned, 0 flagged (selftest 8/8) |
| Executable `.spl` under `doc/06_spec` | `find doc/06_spec -name '*.spl' \| wc -l` | **0** — required |
| Numbered artifact | `numbered-artifact-guard.shs --changed-from origin/main` | OK |
| Direct env/process | `direct-env-runtime-guard.shs --all` | PASS — 0 hits on lane files |
| Skill / rules registry integrity | `check-rules-sdl-integrity.shs` | PASS — 20 gates, registry did not shrink |
| Doc layout / FILE.md manifests | `check-workspace-root-guard.shs` | OK |
| Conflict trees | `check-no-conflict-tree-push.shs` | PASS |
| Conflict markers | `check-no-conflict-markers-push.shs` | PASS |
| File count | `check-tree-size-push.shs` | PASS |
| Test-tree divergence delta | `check-test-tree-divergence-delta.shs` | PASS — 0 introduced |

REQ traceability is carried by `# @req` annotations on every `it` block and
mapped in the plan's traceability table
(`doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md`).

**Lint note:** both system specs fail `simple lint` with
`with_easy_fix`/`with_fix` not found. This is a **pre-existing general linter
defect**, not attributable to this lane — a pre-existing untouched spec
(`test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl`)
reproduces it identically, while this lane's fixtures and admission helper lint
clean. Recorded in the Option bug record.
- [x] AC-9: Landed under `/mnt/data/tmp/simple-main-restart12-push.lock`, linear rebase, one non-force push, remote reachability proven.

## Blocker
No admitted pure-Simple runtime exists on the reference machine.

Fleet sweep 2026-08-16: 1099 binary instances, 19 unique by md5. Fourteen are
the Rust seed (self-identifying, disqualified as this lane's evidence). All five
self-hosted artifacts are non-functional:

| md5 | result |
|---|---|
| `2244f18ce2e6…` | exit 139 on both `compile` and `native-build` (936 copies — the fleet's dominant artifact) |
| `3e268a376d70…` | exit 139 — a second, independent build, identical failure |
| `75fa8f23269a…` | no `test`; SMF compile rc=1; `native-build` rc=0 but emits no artifact |
| `943465748bd1…` | has `test`, but requires delegation to a Rust seed sibling; cannot resolve the SSpec DSL |
| `2b2fa4d057b7…` | Mach-O arm64 — wrong host |

The sole self-hosting fixpoint (stage1 ≡ stage2 ≡ stage3, byte-identical)
segfaults on a three-line hello world. Root-caused this session to the
**`aot:borrow_check`** phase — pinned two independent ways on the stripped
artifact, answering the open question in the tracked record.

Tracked: `.spipe/stage3-segfault-fix/` AC-3 and AC-4, both open;
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.

## Scope Exclusions
- Any change to Engine2D source. The audit concluded none is warranted.
- Any fix to the seed lowering defect — filed, not repaired; it is Rust seed
  code and unverifiable under this lane's evidence rule.
- The rocm `self.backend` hijack asymmetry (`engine.spl` L1700/L1941/L2006) —
  recorded, not patched; different failure direction, unreachable today.
- Phase 4. Untouched throughout.
- Any lane state, skill, or plan owned by another pane — including
  `.spipe/restart12_render_cli_plan_completion/`, which is a different lane.

## Evidence Policy
Pure-Simple self-hosted only. Rust seed output is never counted as evidence for
an acceptance criterion. The seed **was** used once, for a purpose that is not
lane evidence: satisfying the pre-existing repo push gate
`check-native-trailing-default-param.shs`, which requires a working
`native-build` to run at all. Satisfying a push gate is not a runtime PASS and
is not claimed as one.

## Phase
review-done (blocked on runtime for AC-7, AC-8)

## Log
- Fetched `origin/main`, confirmed `f6cadcc36aff`, created isolated worktree
  `/mnt/data/worktrees/simple-restart12-engine2d-font` on branch
  `restart12/engine2d-font-seed-review`. Shared worktree left read-only.
- Verified bootstrap fixpoint (stage1 ≡ stage2 ≡ stage3), then established the
  toolchain blocker in two attempts (`compile`, `native-build`); stopped rather
  than looping.
- Three parallel read-only lanes: fleet binary sweep, stage3 crash root-cause,
  engine2d route audit. All three closed.
- Filed the seed `Option` regression; appended the stage3 phase identification
  and fleet sweep to the existing stage3 record; recorded a pre-existing
  test-tree divergence step-over.
- Authored fail-closed system coverage and knowledge artifacts. No runtime PASS
  claimed for any criterion.
