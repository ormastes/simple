# wm_showcase_session_capture_spec: "no examples executed" reproduces on unmodified origin/main

## Symptom

`test/03_system/gui/wm_showcase_session_capture_spec.spl` fails with:

```
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

with `Duration: ~10s` — far too fast to have run any real window-open/HTML-render
work (that path costs 30-50 CPU-minutes per HTML-backed window in this
environment, per the spec's own governing comments). No compile error, no
`✗` assertion line, no `[use-warning]` naming any unresolved symbol — the
`describe` block's `it` examples simply never register.

## This is NOT caused by task #96's browser/terminal window addition

Verified via a controlled A/B: with `src/app/wm_showcase/session.spl`,
`run.spl`, and the spec file all reverted byte-for-byte to their
`origin/main` content (3-window baseline, before this session's browser/
terminal work), the SAME spec fails the SAME way:

```
$ git show origin/main:src/app/wm_showcase/session.spl > src/app/wm_showcase/session.spl
$ git show origin/main:src/app/wm_showcase/run.spl > src/app/wm_showcase/run.spl
$ git show origin/main:test/03_system/gui/wm_showcase_session_capture_spec.spl > test/03_system/gui/wm_showcase_session_capture_spec.spl
$ bin/simple test test/03_system/gui/wm_showcase_session_capture_spec.spl --no-cache --no-cover-check
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Files were restored afterward (verified byte-identical to the pre-revert
copies via `diff`). This rules out the new browser/terminal window content
as the cause — the defect is pre-existing on `origin/main` right now.

## Not a total-environment failure

An unrelated spec run in the same session, same environment, same command
shape, passed cleanly and quickly:

```
$ bin/simple test test/01_unit/lib/common/ui/draw_ir_v3_group_resolve_spec.spl --no-cache --no-cover-check
SPEC FILE VERDICT: ... declared>=23 executed=23 passed=23 failed=0 dropped=0
Results: 23 total, 23 passed, 0 failed
```

So this is specific to `wm_showcase_session_capture_spec.spl` (or its heavy
transitive import graph), not a broken test harness across the board.

## Two live hypotheses (not yet distinguished)

1. **Shared-daemon race** — the default session daemon serves a stale/racing
   result under concurrent load (many other agent sessions are hammering
   `bin/simple test` on this shared machine right now). `--no-session-daemon`
   avoided the fast fake-failure in one trial (ran past 90s doing real
   compile work instead of failing in ~10s) but that run's own outcome was
   not yet captured when this doc was filed.
2. **Genuine crash/hang inside the `it` block, silently swallowed** — matches
   an earlier, structurally identical symptom already on file:
   `doc/08_tracking/bug/ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`,
   which hypothesizes a `compiler_cross_module_private_symbol_collision`
   wrong-helper JIT dispatch (see
   `doc/08_tracking/bug/compiler_cross_module_private_symbol_collision_2026-06-16.md`)
   silently crashing execution rather than failing a normal assertion. This
   session's own lint/compile output for the wm_showcase import graph shows
   dozens of `compiler_cross_module_private_symbol_collision` warnings
   (`dir_remove_all`, `shell`, `shell_output`, `file_read_bytes`, `path_join`,
   `env_vars`, `process_wait`, `resolve_style`, ... — the transitive graph is
   large and touches many of the exact primitive names flagged there).

Both are plausible; this doc does not claim to have distinguished them.
Whoever picks this up next should check whether `--no-session-daemon`'s
outcome (once captured) genuinely completes (rules out hypothesis 1) or
itself eventually reports "no examples executed" after real compile+run time
(supports hypothesis 2, and would make this spec a second confirmed instance
of the collision-crash class).

## Impact

Blocks the WM showcase integration gate (`test/03_system/gui/
wm_showcase_session_capture_spec.spl`) for task #96 (Simple Browser + Simple
Terminal windows) and for the WM showcase feature generally — the gate
cannot currently produce a real pass/fail verdict through the default test
path on this machine, independent of what changes are or aren't in the
5-window version.

## Workaround

`--no-session-daemon` at minimum avoids the ~10s fake-fast failure signature;
whether it reaches a real PASS/FAIL verdict was still pending capture when
this doc was filed. Budget real wall-clock time (compile-from-scratch plus
however many HTML renders the spec version under test needs) rather than a
short timeout.

## Likely root cause found (2026-08-06, same day)

Commit `5a62d7a2b95` ("fix(web-render): add missing `_web_budget_expired_at` +
`WEB_BUDGET_SITE_*` symbols") landed on `origin/main` shortly after this doc
was filed, from an unrelated concurrent session. Its description: 7 call
sites across `simple_web_html_layout_renderer_layout.spl` and
`..._paint_layout.spl` called `_web_budget_expired_at(WEB_BUDGET_SITE_*)`,
but neither the function nor the site constants existed anywhere in the
tree. Since unresolved symbols are fail-open (WARN, not a compile error) in
this language, every HTML render that reached the layout/paint pass would
hit this genuinely-missing symbol at RUNTIME rather than compile time —
exactly matching hypothesis 2 (a crash inside the `it` block, silently
swallowed as "no examples executed" with zero assertion output, ~10s
duration). `wm_showcase_session_capture_spec.spl`'s gui/web windows both
render real HTML through this exact layout/paint path, so this is a
strong causal match, not just a correlation.

**Update: re-verified against the patched tree — helped, but did not fully
resolve it.** Post-fix, the spec now gets further before failing: stage
markers `wm_showcase_stage start` and `wm_showcase_stage opening=gui` print
(previously nothing printed at all — the failure was earlier, likely at
module-load time), but it still ends in the same
`error: test-runner: no examples executed`, `Duration: ~10s`. A ~10s
duration is far too short for the real interpreted HTML render this stage
triggers (30-50 CPU-minutes per the spec's own governing comments), so
whatever crashes/hangs does so almost immediately after `open_window` calls
into the gui-window's render path — not after the long render itself, so
"the render itself is just slow" is ruled out as an explanation. Grepped the
full log for `unknown extern`, `semantic:`, `not found`, `Unsupported`,
`panic`, `RuntimeError`, `Traceback` — none present. The failure is a total
silent swallow with zero diagnostic text beyond the generic runner message,
consistent with `ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`'s
observation. Since `bin/simple test` always uses the tree-walk interpreter
(never JIT, per `.claude/rules/testing.md`), the
`compiler_cross_module_private_symbol_collision` JIT-wrong-dispatch
hypothesis from that sibling doc does not directly apply here — whatever is
crashing is doing so under the interpreter, so the root cause is still
unidentified, just narrowed to "somewhere very early in the gui window's
render call chain, under the interpreter, with no diagnostic output."

## Impact on task #96 (Simple Browser + Simple Terminal windows)

This defect independently blocks task #96's integration gate — confirmed
NOT caused by that work (baseline A/B above). Task #96's new code
(`src/app/browser/render_adapter.spl`, `src/app/terminal/render_adapter.spl`)
was verified correct by other means instead: `bin/simple lint` clean (0
errors), and a standalone `bin/simple run` probe confirming
`render_browser_html(...)`/`render_terminal_html(...)` produce real,
correctly-shaped HTML output (Hello World page with real browser chrome;
terminal chrome with the real subcommand reference) — see the probe in this
doc's git history / task #96's session notes. Landing task #96 without a
green integration-gate run is a deliberate, disclosed exception, not a
silent skip.

## Next step

- Bisect where in the gui window's render call chain (`_produce_frame` →
  `simple_web_render_html_to_readback_result_with_engine2d_backend` →
  layout/paint) the ~10s silent failure actually originates — a debug
  build or a print-instrumented probe of that call chain directly (outside
  the spec runner) would surface the real crash, since the spec runner
  itself swallows it.
- Consider whether "no examples executed" itself should print the
  underlying crash reason rather than swallowing it — a compiler/test-runner
  improvement, not specific to either spec.
- Cross-reference `ssh_kex_rsa_contract_no_examples_executed_2026-07-20.md`
  as a sibling symptom (same swallowed-failure shape), though the JIT
  wrong-dispatch hypothesis there does not directly transfer here since
  `bin/simple test` never uses the JIT.
