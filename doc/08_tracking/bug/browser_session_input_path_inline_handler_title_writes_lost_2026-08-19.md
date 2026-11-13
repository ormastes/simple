# BrowserSession: input-path inline handlers run but their document.title writes are lost
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-19
- Status: OPEN
- Found while: fixing `[browser-session] ReferenceError: i is not defined / all is not defined`
  (JS engine scope-chain + missing String()/Number()/Boolean(), now fixed — see
  `test/01_unit/lib/js/function_scope_chain_and_global_constructors_spec.spl`)
- Blocks: `test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl`
  (still red after the engine fix; its failure message is clobbered per
  `doc/08_tracking/bug/sspec_hollow_expect_clobbers_failure_message_2026-08-19.md`)

## Symptom

Inline handlers dispatched through the TEXT-EDIT flow execute (pre-engine-fix they
even printed the ReferenceErrors, proving execution), but their `document.title`
mutations never reach `session.current_title`.

Repro (against a page whose textarea has
`onbeforeinput="document.title=document.title+'bi>'"`):

- `session.dispatch_dom_event_route(route, "beforeinput", true, true)` → title gains `bi>` (OK)
- `session._dispatch_dom_input_event_route(route, "beforeinput", true, true, Some("x"), "insertReplacementText")`
  called directly → title gains `bi>` (OK)
- `session.set_dom_text_input_route(route, "zz")` — which internally calls the exact
  same `_dispatch_dom_input_event_route` — → title UNCHANGED (BUG)
- `session.blur_dom_text_input_route(route)` — change/blur/focusout handlers run,
  title UNCHANGED (BUG)

So the loss is specific to `_apply_dom_text_edit_route` / `_blur_dom_focus_route`
composition, not to the dispatch machinery itself. Verified identical behaviour
BEFORE the JS-engine fixes (title already failed to accumulate), so this is
pre-existing, independent of the engine repair. Suspect a stale
`self.runtime_state` copy being written back after the dispatch inside these
composite flows (defect class: interpreter write-back / stale-snapshot clobber),
e.g. `_sync_runtime_body_from_dom` or `_set_dom_text_runtime_state` republishing
state captured before the dispatch.

## Repro scripts

Session-level scripts used for the bisect live at
`/tmp/claude-1000/sessfull.spl`, `/tmp/claude-1000/sessbi2.spl` (scratch; recreate
from this record if gone).



## Addendum 2026-11-11 — lane ne3: LIVE-presumed; runtime verification BLOCKED
## by the known routed P1 seed hazard; no fix commit found

Traversed on work/p3-ne3-20261111 (origin/release/1.0.0 tip 93490a99c5d8),
refreshed seed bin/simple.exe (2026-11-11, build-commit 0791c2b7f4a7), all runs
seed-smoke.

- No commit referencing this bug (grep over `origin/release/1.0.0` history for
  the bug id, "title writes", `_apply_dom_text_edit_route`) identifies a fix.
  The suspected defect class (interpreter write-back / stale-snapshot clobber
  in the composite text-edit/blur flows) is plausibly covered by the 2026-09-01
  chained-`MethodCall` write-back fix (see
  `bytebuffer_struct_param_mutation_not_persisted_2026-09-01.md`), which IS in
  this seed's build — but that is a hypothesis, not evidence for THIS symptom.
- The blocked consumer
  (`test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl`)
  cannot execute on this lane: its single example fails at semantic load with
  `method 'trim' not found on value of type enum in nested call context`,
  preceded by `warning[enum-bare-name-ambiguous]: enum JsValue is registered
  again with a different variant set` (log:
  `build/review/p3fix-ne3-20261111-logs/row3_textarea_lifecycle.log`). Same
  known P1 hazard `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`
  as the sibling fetch-body row; already routed to the seed lane by the lib3
  traverse lane.
- Grant to settle this row: land the seed-lane fix for
  `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`, redeploy the
  seed, then run `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe
  test test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl
  --mode=interpreter --no-cache`. Until then this row stays OPEN/LIVE.


---

## 2026-11-13 triage (live-P3 lane l1, work/live-p3-l1-20261113, base f790f7f266e)

**Titular defect FIXED (first-hand this lane); row stays open on an unrelated residual.**

First-hand evidence (tracked seed `bin/simple.exe`, `--mode=interpreter --no-cache`, this worktree,
log `build/review/l1-textarea-run1.log`): the blocked consumer
`test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl` now **loads and
executes** — the 2026-11-11 nested-call import blocker
(`method 'trim' not found on value of type enum in nested call context`) is gone at this base
(the intermediate-typed-`val` convention is present in the hosted policy file, verified by
direct read). All three **title-accumulation assertions pass**:
`events:focus>` after focus; `events:focus>beforeinput>input>` after
`set_dom_text_input_route`; `events:focus>beforeinput>input>change>blur>focusout>` after
`blur_dom_text_input_route`. The composite text-edit/blur flows therefore no longer lose
inline-handler `document.title` writes — consistent with the 2026-09-01 chained-`MethodCall`
write-back fix the 2026-11-11 addendum hypothesized as the absorber.

The single remaining failure is at the spec's form-encoding assertion (body
`note=Ada+%ED%95%9C%0AB%0D%0A%26+C` vs expected `note=Ada+%ED%95%9C%0D%0A+B+%26+C`) — a
byte-vs-codepoint text-slice scramble after the multibyte `한`, i.e. the **separate,
already-tracked seed defect** `text_len_codepoint_switch_2026-11-03.md` (seed reversal
`a3dfd43c52e` not on release/1.0.0; same signature as the dom_input group-1 failure recorded
in `browser_session_rendering_spec_residual_failures_2026-08-19.md`). It is not the
title-writes defect. Grant to close the spec fully: land the text-slice seed reversal, then
re-run this spec (expect the encoding assertion to be re-judged against the byte-slicing seed).

## 2026-11-13 resolution (P3 triage sweep, work/p3-triage-20261113) — row closed `fixed`

Seed: scratchpad `vkinit/seed-fix`, runs capped `systemd-run MemoryMax=16G timeout 900`, cwd = this worktree at origin/release/1.0.0 `59caff4fd1b`.

Evidence (live, this lane): `test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl` executed=1 passed=1 failed=0 — its title-accumulation assertions (`:85` `events:focus>`, `:93` `...beforeinput>input>` after `set_dom_text_input_route`, `:100` `...change>blur>focusout>` after `blur_dom_text_input_route`) all pass, and the form-encoding residual noted on 2026-11-13 (l1) no longer fails either.
