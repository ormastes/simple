# Lane: l1-pair-b — IDE extension kernel campaign (ex-claude 7e7fdac9)

Goal (verbatim opening directive): "research and make detail plan for pherallel
agents make shared parts done before agents start to prevent conflict each
others. Simple IDE hardening and extension architecture plan" — followed by a
~870-line architecture spec with 10 executive decisions (extension.sdn as the
canonical manifest; typed Simple `activate()` rather than JSON/JS; refactor the
existing `std.editor.extensions` host rather than build a competing kernel; keep
native `app.plugin.registry` separate; Markdown/Word/Sheets/Slides become
trusted built-in extensions; third-party extensions out-of-process by default;
ThemePackage/ThemeRenderSnapshot as the sole theme authority; replace
source-text "system tests" with executable SSpec; MDSOC+ at capsule
boundaries), §14 Waves 0-7 and §15 a 20-item Definition of Done.

Plan docs: `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md`,
`doc/07_guide/app/ide/extension_authoring.md`,
`.spipe/ide_extension_kernel/state.md`.

## Plan audit 2026-08-01

High-integrity lane: the plan was authored, landed, executed by ~20 agents, and
closed with a 20-row per-item commit ledger in which **every claimed sha
verifies on `origin/main`** (`e8276bda`..`14ed678b`, closure `ae51a5aa`, plus a
real second wave `fdeebbc3ba0`..`570436ab484`). The 6 shas not on main are
pre-rebase duplicates, not losses. Kernel, SDN hardening, document service,
four built-in migrations, capability truth, and test de-tautologizing are real
and landed. `activate_event("*")` count is 0; the eager-builtin bug is FIXED.

Still **needs-follow-up**. Actionable next steps, in order:

1. **Close the RE-VERIFY QUEUE.** `.spipe/ide_extension_kernel/state.md` still
   lists 4 harness-blocked specs — `vscode_extension_gen_spec`,
   `capability_truth_spec`, `theme_role_color_spec`, `theme_service_spec`. All
   4 files exist; `bea36f79` and `14ed678b` landed **probe-validated only**.
   Run them on a quiet box and close or re-open the queue.
2. **File the F7 interpreter callback-visibility bug.** Promised in-session; no
   matching record exists under `doc/08_tracking/bug/`.
3. **File L1's four kernel API change requests as tracked todos.** None were
   filed: `LanguageProviderRegistry` has **zero occurrences repo-wide**; typed
   command payloads, `onLanguage` manifest-driven activation, and hot-path
   dispatch are also unfiled.
4. **Finish theme unification (DoD #14).** 8 `ThemeId.IOSLight` hardcodes remain
   in `src/app/office/`; `counter.spl`, `launcher.spl`, `mail/mail_app.spl`,
   `planner/planner_app.spl` are untouched and comments say ThemeService itself
   is not landed. Then close the guest-QEMU theme gate (F2, never run) —
   pre-existing bugs `wm_theme_css_loaded_not_applied_2026-07-20.md` and
   `install_generated_simpleos_wm_theme_dead_2026-07-27.md` are the directive's
   §12 theme completion gate, so no "cross-platform theme complete" claim is
   supportable today.
5. **Scope Wave 6 proper as its own campaign (DoD #9, #19).** Third-party
   extensions are NOT out-of-process: `host.spl:552` returns the status string
   `"ready-external-process"` with no worker protocol, WASM host, or process
   runtime behind it. Wave 6 landed only path containment, default-deny, and
   crash-loop handling. The plan §7 defers "worker/WASM sandbox completion", so
   this is de-scoped rather than dropped — but it is the single largest gap
   against the original directive.
6. **Run the §13 backend-tested / QEMU + board evidence lane.** §14 Wave 0's
   `--feature-check` six-state ladder landed its live states via L7, but the
   backend-tested state and board evidence were never executed
   (`.claude/rules/board-runnable.md` applies).
7. Minor: `test/unit/lib/editor/extension_discovery_contract_spec.spl` still
   uses source-text assertions (DoD #17). Intentional as a contract lint, but
   say so in the doc.

## sspec sufficiency 2026-08-01

**Runner:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`.
The live `bin/simple` (130 MB, Jul-31 12:14) has **no `test`/`run`/`lint`/
`check` subcommands** — the known defect is real and current. Harness
falsifiability was proven at 04:00 (wrong numeric and wrong text oracle both
failed, `3 total, 1 passed, 2 failed`, exit 1). Shared runner findings,
including the Rust-seed delegation, are in `layout_web.md`
§"sspec sufficiency 2026-08-01".

### The 4-spec re-verify queue was RUN — and it CANNOT be closed

| spec | result |
|---|---|
| `test/01_unit/app/vscode_extension_gen_spec.spl` | **TIMEOUT** (exit 124, 300 s, no `Results:` line) |
| `test/01_unit/app/ide/capability_truth_spec.spl` | **TIMEOUT** (exit 124, 300 s) |
| `test/01_unit/lib/common/ui/theme_role_color_spec.spl` | **TIMEOUT** (exit 124, 300 s) |
| `test/01_unit/os/services/theme_service_spec.spl` | **TIMEOUT** (exit 124, 300 s) |

All **4 of 4** produced no verdict — zero passes, zero failures, four timeouts.

**These timeouts are environmental, not spec defects — and that is the
finding.** The discriminator: the 3-example scratch probe that completed in
~60 s at 04:00 was re-run at 04:26 and **timed out at 400 s**. A spec with three
assertions and no imports beyond `std.spec` cannot complete. Contemporaneous
box state: load average 13→18 on 32 cores (peaking at **101** by 05:15),
competing `bootstrap-from-scratch`
builds in sibling worktrees (`simple-redeploy-selfhost-20260731-wt`,
`simple-unresname-fable-wt`) pinning btrfs writeback, with our runner scheduled
at ~2 % CPU. Even `simple test --help` exceeded 120 s.

So the queue's "harness-blocked" label from `bea36f79`/`14ed678b` **still holds
today, for the same reason** — this is not a stale excuse. The correct action is
unchanged: re-run on a genuinely quiet box. Note the earlier window in this same
session (04:02-04:09) *did* produce clean results for other lanes, so the
harness itself is sound; only the box is unusable.

### Coverage verdict

All four queue specs are unit-tier. Repo-wide there is **no system-tier spec for
the extension kernel**: `test/03_system/ide/` exists but holds nothing covering
manifest-driven activation, the capability model, or theme authority.

Assertion quality of the queue is good, not tautological:
`capability_truth_spec` (40 `expect`, 3 `to_contain`, no `file_read`),
`theme_role_color_spec` (28 `expect`, no source-text reads) and
`theme_service_spec` (7 `expect`) are behavioural;
`vscode_extension_gen_spec` uses `file_read` twice against generated output,
which is legitimate for a generator.

Missing scenarios — no spec at any tier:
- **DoD #9/#19 out-of-process third-party extensions.** `host.spl:552` returns
  the string `"ready-external-process"`; grep finds no worker-protocol or
  WASM-host spec exercising it. A spec asserting that status string would be a
  pure tautology — the string is the only implementation.
- **Guest-QEMU theme gate (F2, §12 completion gate)** — never run; the two
  pre-existing theme bugs remain the blocker, so no cross-platform theme claim
  is testable.
- **§13 backend-tested state and board evidence** (`.claude/rules/board-runnable.md`)
   — the `--feature-check` ladder has no backend-tested or board scenario.
- **Typed command payloads, `onLanguage` activation, hot-path dispatch,
  `LanguageProviderRegistry`** — still zero occurrences repo-wide, so the four
  unfiled API change requests have no coverage either.

Correction to item 4 above: `ThemeService` **is** landed
(`src/os/services/theme/theme_service.spl`), and `src/app/office/` now carries
only 2 `ThemeId.IOSLight` hardcodes (`counter.spl`, `launcher.spl`), not 8.

**Verdict: cannot-run** (and insufficient on coverage regardless). The queue
cannot be closed or re-opened on this evidence: three of four specs produced no
verdict at all, and a trivial control spec proves the box — not the specs — is
at fault. Re-run the four on a quiet machine before changing
`.spipe/ide_extension_kernel/state.md`. Even if all four go green, the lane's
largest gaps (out-of-process extensions, theme QEMU gate, board evidence) have
no system test to go green.
