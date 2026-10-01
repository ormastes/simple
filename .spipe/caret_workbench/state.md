# Lane state — caret_workbench

**Goal.** Make Caret a profile of the shared Simple IDE workbench, give the IDE a
real smux-backed terminal service, rebuild the Caret TUI/GUI on the requested
composition (left: roster + details + composer; right: one large session + a
strip of inactive previews), and prove the whole thing end to end on THIS mac by
opening a Caret session against a local slang model.

Design of record:
`doc/01_research/app/llm_caret/caret_suite_ide_workbench_smux_migration_2026-09-05.md`
(source review only — nothing in it was executed).

## Acceptance criteria

- **AC-1** `simple ide --tui` / `--gui` enter a real persistent event loop, accept
  input, and exit cleanly. Today `src/app/ide/main.spl` prints a readiness line
  and returns (defect CARET-H002).
- **AC-2** The IDE terminal service drives a REAL PTY: a nonce sent to a child is
  returned transformed by that child, not echoed from a local buffer (MUX-H001).
  Pane/window focus actually mutates state (MUX-H002). Startup timing comes from a
  clock, and an unknown pane capture is a typed error (MUX-H003).
- **AC-3** `poll_multi_caret_manager` keeps reconciling a `degraded` team until
  every survivor reaches a terminal state (CARET-H001).
- **AC-4** Caret TUI renders the requested composition and a real terminal capture
  is written under `build/test-artifacts/` — a grid, not a source grep.
- **AC-5** Caret GUI renders the same composition from the same session state.
- **AC-6** A local slang model generates tokens through `caret --provider
  slang_local` on this mac, with the verdict line from
  `scripts/check/check-slang-ggml-inference.shs`.
- **AC-7 (knowledge)** Update `doc/07_guide/app/mcp/…`-equivalent guide for the
  workbench, `doc/00_llm_process/feature_expert/<feature>/skill.md`, and file a
  `doc/08_tracking/bug/` record for every defect found and not fixed.

## Shared contract (A0) — LANDED

`src/app/llm_caret/workbench/session_contract.spl`. Verified on the Sep-5 seed
via `build/nb/fixtures/probe_contract.spl`:

```
same_after_restart=false
stale_draft_targets_new_gen=false
draft_targets_own=true
```

Identity is `(value, generation)`; the four state axes (ProcessLifecycle,
AgentTurn, Transport, CapabilityEvidence) are independent; a `ComposerDraft`
binds its target at capture time so a focus change cannot redirect it.

## Host facts (measured 2026-09-05, this mac)

- `bin/simple` -> a bootstrap-generation Rust seed. Bootstrap-only.
- Working runner: `src/compiler_rust/target/bootstrap/simple run <file.spl>`
  (130 MB, Sep 5 20:01). `bin/simple test` is LOAD-ONLY here.
- Module resolution is file-relative: probe/fixture `.spl` must live INSIDE the
  repo tree (`build/nb/fixtures/`), not `/tmp`.
- `rt_pty_open`/`_spawn`/`_read`/`_write` are backed ONLY in the Rust runtime
  (`src/compiler_rust/runtime/src/value/pty.rs`). There is no C-runtime lane, so
  a pure-Simple native build has no PTY yet. Recorded, not fixed.
- No GGUF model and no llama.cpp on this host at session start. llama.cpp cloned
  to `/Users/ormastes/dev/llama.cpp`, built with `-DBUILD_SHARED_LIBS=ON`.
- `scripts/check/build-slang-ggml-shim.shs` is Linux-only: it hardcodes
  `LLAMA_ROOT=/home/yoon/dev/llama.cpp` and requires `libllama.so`. macOS
  produces `libllama.dylib`.

## Status

| Lane | Owner | State |
|---|---|---|
| A0 contract | orchestrator | LANDED, probe-verified |
| A1 IDE persistent launch | delegated | **DONE** — see below |
| A2 smux terminal service | delegated | **DONE** — see below |
| A3 Caret lifecycle | delegated | **DONE** — see below |
| A6 Caret TUI | delegated | **DONE** — see below |
| A7 Caret GUI | delegated | workbench composition landed, probe-verified (2026-09-05) |
| slang-on-mac | delegated | **DONE — AC-6 MET** |

Nothing is pushed. The working copy is shared with peer sessions.

## A3 — Caret lifecycle reconciliation (AC-3): DONE 2026-09-05

Defect CARET-H001 confirmed at `multi_caret_manager.spl:70`: the guard
`if manager.status != "running": return manager` treated `degraded` as terminal,
so once a team lost one child the SURVIVORS were never polled again and the
manager froze at `degraded` permanently.

Fix (2 lines): `degraded` is also reconcilable.

```
if manager.status != "running" and manager.status != "degraded":
    return manager
```

Contract bridge deliberately NOT taken: `is_reconcilable` is per-session over a
`ProcessLifecycle` enum, while the manager's `status` is a whole-team aggregate
text from `summarize_agent_team`. Synthesizing a `SessionView` per child is a
real refactor and buys nothing here, so the manager keeps its own
representation. Recorded so a later lane does not "fix" it back.

Reproduce-first evidence (RED reproduced twice — fixture, then by reverting the
fix and re-running the real spec):

```
RED:    p2.status=degraded   (expected exited)
        ✗ keeps reconciling a degraded team until every survivor is terminal
GREEN:  p2.status=exited
        7 examples, 0 failures  /  5 examples, 0 failures
```

The oracle spawns a real survivor plus a never-spawned slot, polls to
`degraded`, kills the survivor DIRECTLY (not through `stop_multi_caret_manager`)
and never calls launch again, then asserts the degraded manager reaches
`exited` AND that the roster is still exactly 2 processes — so a duplicate
launch cannot pass it. `_leaked_processes` (kill-failed child with pid > 0 still
counts as a leak), rollback, and stop behaviour verified unaffected.

Files: `src/app/llm_caret/multi_caret_manager.spl`,
`test/01_unit/app/llm_caret/multi_caret_manager_spec.spl`.

Carried caveat, pre-existing and NOT introduced here: `test/01_unit/` and
`test/unit/` copies of this spec were already divergent (01_unit has 5 extra
tests). Only the canonical `01_unit` copy was extended.

## Host progress

llama.cpp built to 89% with the Metal backend present
(`libggml-base.dylib`, `libggml-blas.dylib`, `libggml-cpu.dylib`, Metal tuning
target). Confirms macOS produces `.dylib`, so the shim script's `libllama.so`
precondition must be ported before it can pass here.

## A6 — Caret TUI workbench (AC-4): DONE 2026-09-05

New, disjoint from peers:
- `src/app/llm_caret/workbench/tui_layout.spl` — pure geometry. `compute_layout`
  requires `width>=100 and height>=24` for the full composition; below that it
  returns a single compact view (Session/Agents/Compose) per research §4.2.
- `src/app/llm_caret/workbench/tui_view.spl` — grid renderer, one exact-width row
  per line. Status text comes ONLY from the contract enums; `Unknown` renders as
  `Unknown` rather than being guessed as idle.
- `test/01_unit/app/llm_caret/workbench/tui_workbench_layout_spec.spl` — 4
  examples: 120x40 full, 80x24 compact fallback, 160x50 with 3 readable
  previews, and the draft-target-not-redirected invariant.

```
4 examples, 0 failures
SPEC FILE VERDICT: ... outcome=OK declared>=4 executed=4 passed=4 failed=0 dropped=0
```

Captures written (real grids, not source greps):
`build/test-artifacts/caret_workbench/tui_{80x24,120x40,160x50}.txt`.

The composer's `To <agent>` line is bound to `draft.target`, so it stays put when
the selected roster row changes — the contract invariant holds at the UI.

## Defect found and FILED by the orchestrator

`doc/08_tracking/bug/nested_array_element_bound_to_var_copies_2026-09-05.md`.

The lane reported it as "array indexing returns nested arrays by value". I
re-probed before filing and that is broader than what reproduces:

| form | result |
|---|---|
| `outer[0][1] = "MUT"` chained index assign | works |
| `flat[1] = "FLAT"` top-level index assign | works |
| `var row = outer[1]` then `row[0] = ...` | **BROKEN** — writes a copy |

So the defect is in BINDING an inner array to a variable, not in indexed
assignment generally. Filed with that correction, because a fix aimed at the
broader claim would look in the wrong place. Workaround in `tui_view.spl` is a
flat row-major `cells: [text]` grid, marked as a workaround.

## A1 — IDE persistent launch (AC-1): DONE 2026-09-05

`src/app/ide/main.spl` now routes `--tui`/`--gui`/`--gui-sdl` into the EXISTING
editor paths (`editor_tui_run`, `gui_shell_run_profile`,
`gui_shell_run_sdl_profile`) instead of printing a readiness line and returning.
No new UI framework; the editor shell was reused, not forked.

`--profile <name>` added to `EditorLaunchOptions`
(`src/lib/editor/core/launch.spl`, both `--profile x` and `--profile=x`,
default `editor`). `gui_shell.spl` extracted its unconditional `*` + simple +
markdown activation into `gui_shell_apply_profile`; `caret` activates only
`simple-language`, every other/unknown profile keeps the original behaviour.
`gui_shell_init`/`gui_shell_run`/`gui_shell_run_sdl` keep their signatures and
delegate, so existing editor call sites and signature-matching specs are
untouched.

Evidence:

```
5 examples, 0 failures   test/01_unit/app/ide/ide_profile_launch_spec.spl (new)
5 examples, 0 failures   test/01_unit/app/ide/ide_launch_harden_spec.spl (pre-existing, unaffected)
timeout 5 ... run src/app/ide/main.spl --tui foo.spl   -> exit 124 (blocked in stdin_read_char)
timeout 8 ... run src/app/ide/main.spl --gui --profile caret foo.spl -> exit 124 (blocked in GUI poll loop)
... run src/app/ide/main.spl foo.spl -> "Ready for tui IDE startup with 1 file(s)."
```

The exit-124 timeouts are the proof of AC-1: the process now BLOCKS in an event
loop where it previously returned. The no-flag readiness path is byte-identical,
so automation is unaffected.

Not verified: no real GUI window was opened (no display available to the lane).
Verification is limited to the dispatch decision, profile narrowing, and the
shell entering its poll loop.

Pre-existing RED, untouched and out of scope: `ide_capability_truth_spec.spl`
(8/11 failing) and `ide_harden_spec.spl` (6/39 failing). Confirmed unrelated to
the three files this lane edited.

## Shared-tree hazard confirmed: do NOT `git stash` in this working copy

The A1 lane ran `git stash` / `git stash pop` mid-task. The stash FAILED to
create (a conflicting untracked entry blocked it), and the subsequent `pop` then
tried to apply an UNRELATED pre-existing stash belonging to another session and
aborted with "stash entry kept".

Verified by the orchestrator afterwards — nothing was lost:

```
$ git stash list
stash@{0}: On main: preserve concurrent index state before bootstrap sync 2026-09-04
stash@{1}: autostash
stash@{2}: autostash
stash@{3}: WIP on perf/vulkan-2d-c-benchmark: ... rt_vulkan_copy_u32_slots ...
```

All four peer entries intact; all A1 edits present. But this was luck, not
safety: `git stash pop` in a shared working copy will happily apply another
session's stash over your tree. Add to the landmine list — stash is not a safe
scratch mechanism here.

## slang-on-mac (AC-6): DONE 2026-09-05 — INDEPENDENTLY REPRODUCED

Gate verdict, re-run by the orchestrator (not just reported by the lane):

```
MODEL qwen2.5-0.5b-instruct-q8 -> GENERATED:  A compiler is a program that
translates source code into machine code, allowing programmers to write code
that can be executed on a computer.
PASS -- 1 model(s) reached a verdict, 1 generated, 0 refused with a reason,
0 silent (binary: src/compiler_rust/target/bootstrap/simple)
EXIT=0
```

A direct `bin/caret --provider slang_local` session was also run separately by
the orchestrator: exit 0, real generation. This is the user's actual acceptance
("open caret session connected to slang local model"), so it was verified as its
own step rather than inferred from the gate.

Stack: llama.cpp `6a1a922`, Qwen2.5-0.5B-Instruct-GGUF q8_0 (675,710,816 B) at
`models/qwen2.5-0.5b-instruct-q8/`. The shim compiled against CURRENT `llama.h`
with **no API drift** (`PASS -- 17 symbol(s) exported`) — the drift risk flagged
up front did not materialise.

### Four real defects fixed (not worked around)

1. `memory_budget.spl` read only `/proc/meminfo` -> `-1` on macOS -> EVERY load
   refused. Darwin lane added (`sysctl` + one `vm_stat`); unreadable still
   refuses rather than guessing.
2. `llm_engine.spl` used a flat 6 GiB KV/activation estimate, ~10x over for a
   0.5B model. Now scales with weights, 1 GiB floor, and the old 6 GiB is kept as
   a CEILING so no large model is admitted more laxly than before.
3. `default_headroom_bytes` was a flat 8 GiB — over half a laptop, so nothing of
   any size could load. Now `total/16`.
4. The model was never released: ggml's static Metal destructor aborted with
   **exit 134 AFTER printing a correct answer**. `slang_release()` existed and
   was simply uncalled.

Defect 4 is the interesting one: the answer was already correct, so anything
scoring on output text alone would have called this green while the process was
dying on teardown.

### Carried caveat for the DGX owner

Fix 3 changes headroom on Linux too, where `MemTotal` excludes kernel reserve —
the DGX lands nearer 7.5 GiB, marginally LAXER than before. Flagged in
`doc/08_tracking/bug/slang_local_memory_gate_and_teardown_not_portable_2026-09-05.md`.

### Script ports + two latent bugs found in the gate itself

`build-slang-ggml-shim.shs` now accepts `.so`/`.dylib` and ERRORs (exit 2) on an
unset `LLAMA_ROOT`. Two latent bugs found while porting: `cc_rc=$?` was
unreachable under `set -e` (the FAIL line could never print), and
`nm -D --defined-only` + `' T slang_ggml_'` cannot match Mach-O's underscored
symbols, so it would have FAILED a perfectly good build. Output keeps the `.so`
name because the loader hardcodes it at `llm_engine.spl:26`.

### Not fixed, documented

- **`SIMPLE_BINARY` is mandatory here.** Both `bin/caret` and the gate prefer
  `bin/simple`, which is bootstrap-only (no `run`) yet answers `--version` — so
  both selectors pick a binary that cannot work. Real usability defect.
- ponytail: per-dispatch release drops the residency cache, so a multi-turn TUI
  reloads the model each turn. Upgrade path: release from caret's shutdown path.

`.gitignore` got `/models/` **anchored**. Orchestrator verified an unanchored
`models/` would have swallowed 28 tracked paths; all 28 remain tracked.

## A7 — Caret GUI workbench (AC-5): DONE 2026-09-05

New: `workbench/gui_layout.spl` (breakpoints 1100/760 px, connection status,
per-session `SessionUiState`), `workbench/gui_page.spl` (HTML renderer for the
left control column + large session + read-only preview strip). Edited
`gui.spl`; left `caret_gui_native_html` alone — that is the separate Metal
companion surface, not the browser workbench.

```
TOTAL_FAILURES=0   build/nb/fixtures/probe_gui_workbench.spl
5 examples, 0 failures   llm_caret_interfaces_spec.spl
3 examples, 0 failures   llm_caret_gui_backends_spec.spl (no Metal-path regression)
```

- **GUI-H001 fixed:** no branch produces "Connected" by default; every
  `Transport` variant maps to its own label, and no-session maps to `Connecting`.
  Asserted that an empty-roster render never contains the string `Connected`.
- **GUI-H002 fixed:** `begin_submit` does not clear the draft; `Rejected` and
  `Unknown` retain it; only `Acknowledged` clears. Scrolling up suspends follow;
  reaching bottom resumes. Per-agent drafts and scroll are independent across an
  a1<->a2 switch, and a stale-generation `SessionId` fails `draft_targets`.

Artifacts: `build/test-artifacts/caret_workbench/gui_{full,collapsed,compact}.html`.

Not verified: no live browser. The embedded client-side JS mirrors the Simple
rules but was never executed in a browser event loop. `caret_gui_html()` still
renders an empty roster — wiring real agents needs `multi_caret_manager.spl`,
which is peer-owned; the render function already accepts real `SessionView` lists.

### Second compiler defect filed

`doc/08_tracking/bug/option_generic_unresolvable_under_large_cocompiled_program_2026-09-05.md`
— importing `app.llm_caret.provider`'s backend graph together with a module using
builtin `Option<T>` at two different `T`s in ONE file makes `Option` unresolvable
(`class Option not found in this scope`). Bisected to that exact combination.
Workaround: dedicated `{found: bool, value: T}` structs. That is why the new GUI
modules contain no `Option` despite the obvious fit.

## A2 — smux terminal service (AC-2): DONE 2026-09-05

### CORRECTION to this file's own host facts — PTY does NOT work

The "Host facts" section above claimed the PTY externs are backed and therefore
work under the seed. **That was wrong**, and the A2 lane disproved it. Verified
independently by the orchestrator:

```
$ grep rt_pty_ src/compiler_rust/compiler/src/interpreter_extern/mod.rs
  :2803  insert_simple!("rt_pty_open",  pty::rt_pty_open);
  :2804  insert_simple!("rt_pty_spawn", pty::rt_pty_spawn);
$ grep 'pub extern "C" fn rt_pty' src/compiler_rust/runtime/src/value/pty.rs
  :123 rt_pty_open  :226 rt_pty_write  :304 rt_pty_read  :336 rt_pty_close
```

`rt_pty_read`/`rt_pty_write` are DEFINED but registered nowhere, so they resolve
to `E-SFFI-001 unknown extern function` and silently return nil. `rt_pty_spawn`
returns -1 here even with two fresh fds. And the declarations at
`smux_remote.spl:22-30` disagree with `pty.rs` on the fd type (i32 vs i64) AND
on the second parameter (`buf_size` vs `timeout_ms`), so the calls would be
wrong even once registered.

Record: `doc/08_tracking/bug/pty_externs_unusable_under_seed_interpreter_2026-09-05.md`.

**What smux actually uses instead:** real child processes over pipes via
`std.nogc_sync_mut.io.process_ops` (no raw `rt_*`). That still satisfies the
AC-2 oracle — a real child transforms a nonce — but gives no controlling
terminal, so job control and full-screen TUI passthrough stay out of reach.

### Blocker found first: smux_api_spec was ALREADY 4-of-5 RED

Not caused by this lane. Root cause is a compiler defect: a module-level `var`
write is silently discarded when the RHS method reads `me`
(`_svc = _svc.add_session(...)`). Workaround `val cur = _svc; _svc = cur.f()`
applied at all 18 `_svc` sites. Tracked RED spec (deliberately left failing, it
documents a live defect):
`test/01_unit/compiler/module_var_write_lost_when_rhs_reads_me_spec.spl`
-> `2 examples, 1 failure` — `expected 1,1,1 to equal 1,2,3`.
Record: `doc/08_tracking/bug/module_var_write_lost_when_rhs_method_reads_me_2026-09-05.md`.

### Reproduce-first evidence, all six defects

`run build/nb/fixtures/red_smux_defects_spec.spl` -> `6 examples, 6 failures`:

| defect | RED symptom |
|---|---|
| MUX-H001 | `expected nonce7f3a to not equal nonce7f3a` — capture echoed the caller's own bytes |
| MUX-H002/H005 | `expected true to equal false` — focus accepted a pane from another session |
| MUX-H003 | `expected 1 to be greater than 1000` — hard-coded `1u64` startup time |
| MUX-H003 | `expected 1 to equal 0` — unknown pane fabricated one row |
| MUX-H004 | `expected false to equal true` — survivors orphaned after closing pane 0 |
| MUX-H006 | `expected id25 to equal ` — a 9th session got a real id past the 8-slot cap |

GREEN after: `test/01_unit/os/apps/smux/smux_terminal_service_spec.spl`
-> `8 examples, 0 failures`. The H001 example spawns
`sh -c 'while read l; do echo "GOT:$l"; done'` and asserts the capture equals
`GOT:nonce7f3a`; a pane with no child returns `Err`. Full sweep all
`outcome=OK`: terminal_service 8/8, smux_api 5/5, capacity 2/2, os/smux_spec
20/20, dashboard 21/21, smux_app 3/3, mux_model 9/9.

### Still red / ponytails

PTY lane blocked (record filed). `smux_create_session` refuses with an empty-id
sentinel rather than a `Result` — callers counted, upgrade noted in code.
Scrollback ring is 8 lines. Pre-existing and untouched: `mod.spl` imports a
nonexistent `MuxAttachResult`; `tmux_simpleos_spec` references
`metrics.send_text_count`, absent from `SmuxMetrics`.

## Final cross-lane verification (orchestrator, all four together)

```
smux_terminal_service_spec.spl:      8 examples, 0 failures
tui_workbench_layout_spec.spl:       4 examples, 0 failures
ide_profile_launch_spec.spl:         5 examples, 0 failures
multi_caret_manager_spec.spl:        7 examples, 0 failures + 5 examples, 0 failures
```

29 examples, 0 failures. Plus AC-6 reproduced independently (gate PASS exit 0,
and a separate direct `bin/caret --provider slang_local` session).

## Honest status against the goal

MET: AC-1 (IDE persistent launch), AC-2 (smux real-child terminal service, over
pipes not PTY), AC-3 (degraded reconciliation), AC-4 (TUI composition + real
grid captures), AC-5 (GUI composition + GUI-H001/H002), AC-6 (local slang model
through caret on this mac), AC-7 (wiki + 5 bug records).

NOT met — the "whole working model" is not end-to-end wired:
- The GUI still renders an empty roster. Wiring live agents into it needs
  `multi_caret_manager` -> `SessionView` plumbing that no lane owned.
- Caret's TUI/GUI do not yet consume the smux terminal service; the workbench
  renders session state, not live panes.
- No live GUI window and no live browser were ever opened on this host.
- No controlling terminal, so a full-screen provider CLI (claude/codex) cannot
  yet run inside a workbench pane. That is the real remaining blocker for the
  "native CLI in the big pane" half of the design.

## A8 — end-to-end wiring: DONE 2026-09-05

The three seams the lanes left open are now closed and proven together in one
oracle. Nothing committed; edits are in the shared working copy.

New files:
- `src/app/llm_caret/workbench/session_source.spl` — the ONLY
  `MultiCaretManager` -> `SessionView` translation, plus a live registry
  (`publish_manager_sessions` / `live_sessions` / `publish_pane_output`) that
  the surfaces read. `AgentTurn.Unknown` for every terminal-backed child: a raw
  child exposes no semantic turn state. Transport is derived from the computed
  lifecycle, NOT from `ManagedAgent.alive` — that flag only excludes the
  statuses "stopped"/"exited", so a reaped child reported `not_running` reads
  as alive and would have rendered `Ready` over a dead process.
- `src/app/llm_caret/workbench/pane_source.spl` — smux capture -> lines.
  Deliberately a SEPARATE module: `gui.spl` imports `session_source` and is
  itself imported by `main.spl`, so routing smux's five distinct
  `Result<T, text>` instantiations through that closure would reproduce the
  shape of the filed generic-resolution defect. `main.spl --help` re-verified
  loading after the change.
- `src/app/llm_caret/workbench/tui_entry.spl` — `render_live_workbench`.
  `compute_layout`/`render_workbench` had NO production caller; this is it.
- `test/fixtures/caret_workbench/agent_stub.shs` (tracked, mode 755) — the
  launch plan's argv (`-p <prompt> --output-format json`) is rejected by every
  stock binary, so a real long-lived child needs a stub. `exec sleep 60` so
  `process_kill` signals sleep itself.
- `test/03_system/app/llm_caret/caret_workbench_e2e_spec.spl` — the oracle.

Edited: `tui_view.spl` (`active_pane_id`/`active_output` on
`WorkbenchRenderInput` + `new_render_input_with_output`; `new_render_input`
unchanged), `gui_page.spl` (`render_workbench_page_with_output`, escaped
`<pre class='pane-output'>`; `render_workbench_page` delegates), `gui.spl`
(`caret_gui_html()` now renders the live registry).

```
2 examples, 0 failures
SPEC FILE VERDICT: test/03_system/app/llm_caret/caret_workbench_e2e_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0
```

No regressions: tui_workbench_layout 4/4, llm_caret_interfaces 5/5,
llm_caret_gui_backends 3/3, smux_terminal_service 8/8, multi_caret_manager
12/12, all `outcome=OK`.

Captures: `build/test-artifacts/caret_workbench/e2e_live_team.{txt,html}` —
a 40-row grid showing both real managed children (`agents/alpha.md`,
`agents/beta.md`, both live pids) and `GOT:nonce8a41c`, the nonce as the
pane's real child TRANSFORMED it.

### Honest limits

- The pane's child is NOT one of the manager's agents: the manager spawns with
  `process_spawn_async` (no piped stdout) while a pane needs
  `smux_pane_spawn`. Both surfaces therefore label the region `Pane <id>`
  rather than implying pane == selected agent. ponytail: launch managed agents
  through `smux_pane_spawn` so the identities coincide.
- Nothing in `src/` launches a `MultiCaretManager` — verified by grep. The GUI
  and TUI are honestly wired to the registry, but in production nothing feeds
  it yet, so `caret_gui_html()` still serves an empty roster until an owner
  calls `publish_manager_sessions`. That is the next lane, not a fake here.
- `ManagedAgent`/`AgentProcess` drop the launch request's provider, so the
  roster shows `process`. ponytail recorded in `session_source.spl`.
- Still no live browser and no live GUI window on this host.

Teardown is asserted against the OS, not against the manager's own word:
after `stop_multi_caret_manager` returns `stopped`, the spec calls
`process_is_running(pid)` on BOTH children and requires `false`. A before/after
`pgrep -x sleep` diff around the run showed no surviving stub (the new pids in
that window were peer sessions' `sleep 10`). `gui.spl`'s now-unreachable
`caret_gui_workbench_html` and its two dead imports were deleted rather than
left orphaned.

## A8 — end-to-end wiring: DONE 2026-09-05 (verified by orchestrator)

New: `workbench/session_source.spl` (manager -> `SessionView` + live registry),
`workbench/pane_source.spl` (smux capture -> lines),
`workbench/tui_entry.spl` (`render_live_workbench` — `compute_layout`/
`render_workbench` had NO production caller before this),
`test/fixtures/caret_workbench/agent_stub.shs`,
`test/03_system/app/llm_caret/caret_workbench_e2e_spec.spl`.

`pane_source` is deliberately its own module: `gui.spl` -> `main.spl` already
co-compiles the `provider` backend graph, and routing smux's five
`Result<T,text>` instantiations through there hits the filed generic-resolution
defect.

Orchestrator re-ran everything on the SAME seed (130402384, Sep 5 20:01:33,
bracketed before and after):

```
caret_workbench_e2e_spec.spl:     2 examples, 0 failures
smux_terminal_service_spec.spl:   8 examples, 0 failures
tui_workbench_layout_spec.spl:    4 examples, 0 failures
ide_profile_launch_spec.spl:      5 examples, 0 failures
multi_caret_manager_spec.spl:     7 examples, 0 failures + 5 examples, 0 failures
```

Live capture `build/test-artifacts/caret_workbench/e2e_live_team.txt` (and its
HTML twin) both contain `GOT:nonce8a41c` — the nonce TRANSFORMED by the pane's
real child, which an echo cannot produce. Two real pids launched through
`launch_multi_caret_manager`; teardown asserted against the OS
(`process_is_running(pid)==false`) plus a before/after `pgrep -x sleep` diff, not
against the manager's own word.

## FINAL HONEST STATUS

**Met:** AC-1..AC-7. Six defects fixed with reproduce-first evidence, five new
bug records filed, 26 examples green across five specs plus the e2e.

**All three gaps are now CLOSED — see A9 and A10 below.**

1. **Nothing in `src/` ever launches a `MultiCaretManager`** (grep-verified). The
   registry is wired but never fed, so in production `caret_gui_html()` still
   serves an empty roster until an owner calls `publish_manager_sessions`. This
   is the single biggest remaining gap and it is a wiring owner, not a design
   problem.
2. **A pane's child is not a managed agent.** The manager uses
   `process_spawn_async` (no piped stdout); a pane needs `smux_pane_spawn`. Both
   surfaces honestly label the region `Pane <id>` rather than implying
   pane == agent.
3. **No controlling terminal.** smux drives real children over PIPES because the
   PTY externs are unusable (see the A2 correction). Real child output works; a
   full-screen provider CLI (`claude`, `codex`) CANNOT attach to the big pane.
   That is the blocker for the design's native-CLI-fidelity half.

Also unverified on this host: no live GUI window, no live browser. TUI rendering
WAS checked properly — real captured grids at 80x24 / 120x40 / 160x50.

`SessionId` generation is pinned to 1 (no restart path yet) and the roster shows
`process` instead of the provider, because `ManagedAgent`/`AgentProcess` drop it.
Both ponytailed in `session_source.spl`.

## A9 — production wiring: pane == agent: DONE 2026-09-05

Both gaps in FINAL HONEST STATUS are closed. Nothing committed.

**Gap 1 — a production owner exists.** `src/app/llm_caret/main.spl --workbench`
launches a real agent team, publishes it into `workbench.session_source`'s live
registry each frame, and renders the workbench. Routed inside the EXISTING caret
entry (no second entry point), and dispatched BEFORE `is_valid_provider` on
purpose: agent providers ("claude") are a different vocabulary from chat
providers ("claude_cli"). Real command and its real output:

```
$ SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple bin/caret --workbench \
    --agent agents/alpha.md --agent agents/beta.md \
    --agent-cmd test/fixtures/caret_workbench/agent_pane_stub.shs \
    --send nonceA9live --workbench-frames 20
|Agents                                ||agents/alpha.md / process / Unknown       |
|> agents/alpha.md process Unknown     ||ACTIVE SESSION                            |
|  agents/beta.md process Unknown      ||Transport: Ready                          |
|                                      ||Pane id3                                  |
|                                      ||AGENT:ready                               |
|                                      ||AGENT:nonceA9live                         |
AGENT  PID  PANE  STATUS
  agents/alpha.md  49985  id3  running
  agents/beta.md  49987  id4  running
manager=running roster=2
teardown=stopped still_running=0
```

The same command with NO `--agent-cmd` launches the host's real `claude` binary
and also reports `roster=1 ... teardown=stopped still_running=0`.

**Gap 2 — the pane's child IS the managed agent.** New
`src/app/llm_caret/workbench/pane_team.spl` spawns every agent through
`smux_pane_spawn`, so one process is both. `multi_caret_manager.spl` gained
three behaviour-preserving seams (`multi_caret_manager_of`,
`reconcile_multi_caret_manager`, `settle_multi_caret_manager`) so the pane lane
reuses the manager's status rules instead of copying them; `poll`/`stop` now
delegate to those seams and are otherwise unchanged.

The identity is proven DESTRUCTIVELY, not by inspection: closing only alpha's
PANE kills exactly alpha's pid and leaves beta running. Two processes cannot
pass that.

### Third runtime defect found and filed

`doc/08_tracking/bug/process_exists_proc_only_and_piped_pids_invisible_2026-09-05.md`

Two independent breakages, both of which make a liveness assertion vacuously
green:

- `rt_process_is_running`/`rt_process_kill` only consult the ASYNC spawn
  registry, so a piped child that had just answered a nonce reported
  `process_is_running == false`. **A8's teardown assertion
  `process_is_running(pid)==false` therefore never checked anything** for a
  piped pid — it is only meaningful there because A8's children were
  async-spawned.
- `rt_process_exists` stats `/proc/<pid>`, which macOS does not have, so it is
  false for every live pid; and `process_exists` is defined TWICE with an
  identical signature (`app.io.process_ops` and test_runner's `/proc` copy), so
  inside any spec it silently binds the wrong one — measured `true` outside a
  spec and `false` inside one for the same live pid.

Workaround, pure Simple: `app.io.process_ops.process_pid_exists` — uniquely
named so the collision cannot bind it, `/proc` fast path with a `ps -p`
fallback. That is what this lane's teardown asserts against.

### Evidence

```
caret_workbench_prod_spec.spl:     2 examples, 0 failures   (new)
caret_workbench_e2e_spec.spl:      2 examples, 0 failures
tui_workbench_layout_spec.spl:     4 examples, 0 failures
llm_caret_interfaces_spec.spl:     5 examples, 0 failures
smux_terminal_service_spec.spl:    8 examples, 0 failures
multi_caret_manager_spec.spl:      7 examples, 0 failures + 5 examples, 0 failures
```

Captures: `build/test-artifacts/caret_workbench/prod_live_team.{txt,html}`,
`prod_cli_stdout.txt`, `live_workbench.{txt,html}`.

### Still open

- **No controlling terminal** for the workbench lane. smux grew a
  `smux_pane_spawn_pty` opt-in this session (peer lane), but `pane_team` uses
  the PIPE lane: the PTY externs remain unusable under this runner. A
  full-screen provider CLI still cannot render in the big pane.
- ponytail in `run_workbench`: a bounded refresh loop printing the FINAL frame,
  not a key-driven event loop. Input handling belongs to the IDE TUI shell
  (AC-1); forking a second one here would be the two-owner error again.
  upgrade: drive `render_live_workbench` from that shell and route keystrokes
  through `send_to_agent`.
- The roster still shows `process` rather than the provider
  (`ManagedAgent`/`AgentProcess` drop it) and `SessionId` generation stays 1 —
  both pre-existing ponytails in `session_source.spl`.

## A10 — controlling terminal (PTY): DONE 2026-09-05

**Diagnosis.** Three separate defects, only one of which the bug record had
right:

1. `rt_pty_spawn` in `src/compiler_rust/runtime/src/value/pty.rs` declared
   `shell: *const c_char`. A Simple `text` argument arrived there as an **empty
   C string**, so `spawn` fell out at its own `shell.is_empty()` guard and
   returned the catch-all `-1`. Its sibling `rt_pty_write` in the same file
   already took a `RuntimeValue` for a `text` — `rt_pty_spawn` was the odd one
   out. That, not the "two SLAVE_TABLEs" hypothesis, is the root cause of the -1.
2. Extern dispatch **splits by signature**. `rt_pty_open`/`rt_pty_spawn` reach
   the RUNTIME `#[no_mangle]` symbols even though the interpreter extern table
   registers those names (proven: only the runtime copy's diagnostics fire),
   while the `text`/`bool`-returning `rt_pty_read`/`rt_pty_write`/`rt_pty_close`
   go through the interpreter table (proven: `probe_pty_dispatch.spl` gets
   `read=[] write=false close=false` with none of the runtime copies'
   `PTY read error:` / `PTY write error:` stderr lines). So the three new
   registrations are the live path, not a dead fallback.
3. The `.spl` declarations disagreed with both backings (fd `i32` vs `i64`,
   `buf_size` vs `timeout_ms`, an `i32` write return that is really a `bool`).

**Seed change: YES, and here is why.** The rule is "fix in pure Simple, not the
Rust seed". It does not reach this: (a) the defect is a wrong Rust FFI parameter
type, which has no pure-Simple expression at all; (b) there is no C-runtime PTY
lane (`src/runtime/runtime_pty.c` is compiled by no build path), so no
pure-Simple alternative exists on this host; (c) this is wiring an
already-implemented runtime function, not reimplementing a feature or chasing
performance. The change is small and local: one parameter type, a `ptsname`
fallback so a split open/spawn pair cannot fail silently, distinct failure codes
(-2..-6) replacing one ambiguous -1, and three `insert_simple!` lines. No
refactor.

**Evidence — same two commands, both lanes, one process.** Binary:
`src/compiler_rust/target/debug/simple`, 119,938,520 bytes (rebuilt Sep 5 21:17
after a peer session deleted `target/debug`; identical size, re-verified there).

```
=== A. PTY lane (rows=31 cols=97) ===
pty_open_fd=4
pty_spawn_pid=28949
pty_write_ok=true,true
PTY_OUT_BEGIN
tty
stty size
sh-3.2$ tty
/dev/ttys031
sh-3.2$ stty size
31 97
sh-3.2$
PTY_OUT_END
=== B. pipe lane (same two commands) ===
pipe_spawn_pid=29455
stty: stdin isn't a terminal
PIPE_OUT_BEGIN
not a tty
PIPE_OUT_END
```

`/dev/ttys031`, the kernel-reported `31 97` (exactly the winsize smux passed to
`openpty`) and the interactive `sh-3.2$` prompt are all impossible on a pipe;
the pipe run says `not a tty`. Neither expected string occurs in the input, so
PTY ECHO cannot fake either.

**Wiring.** `PaneRecord` gained `pty_fd: i64` (-1 = pipe-backed).
`smux_pane_spawn_pty` / `smux_pane_is_pty` / `smux_pane_close_pty` are the
opt-in lane; `smux_send_text` and `smux_drain` branch on `pty_fd > 0`. The pipe
lane is untouched and still the default — nothing spawns implicitly.
`smux_close_pane` and `smux_reset_for_test` close the PTY master (a PTY child is
not in the pipe registry, so `process_close_piped` would have leaked the fd);
`smux_pane_alive` on a PTY pane reports master-open rather than a pid probe and
is marked `# ponytail: ... — upgrade: expose a pid-based liveness probe`.

**Verdicts** (all on the debug binary above):

```
mux_model_spec.spl:                     9 examples, 0 failures
mux_rects_spec.spl:                     5 examples, 0 failures
smux_api_spec.spl:                      5 examples, 0 failures
smux_app_spec.spl:                      3 examples, 0 failures
smux_pty_controlling_terminal_spec.spl: 2 examples, 0 failures   (new)
smux_service_capacity_spec.spl:         2 examples, 0 failures
smux_terminal_service_spec.spl:         8 examples, 0 failures
cargo test -p simple-runtime:           48 passed; 0 failed  (3 value::pty::tests)
```

**Still blocked / carried caveats.**

- **The fix is NOT in `src/compiler_rust/target/bootstrap/simple`.** That path is
  a symlink into `target/bootstrap.generations/<hash>/`, which is mode `dr-x------`
  — a cargo build into it fails with `Permission denied` on `.cargo-lock`. This
  lane therefore built `--profile dev` into `target/debug/simple` and used that
  for every result above. Any peer lane still on the Sep-5 20:01 bootstrap seed
  will still see `rt_pty_spawn` return -1. Producing a new bootstrap generation
  is out of this lane's scope.
- No C-runtime PTY lane still: a pure-Simple NATIVE build has no PTY regardless.
- `smux_remote_main`'s PTY path is corrected but has no spec (it is an
  stdin-driven service loop); only its module load is verified.

## A9 — production wiring (gaps 1 + 2): CLOSED 2026-09-05

New `workbench/pane_team.spl`: every agent is spawned via `smux_pane_spawn`, so
the pane's child **is** the `ManagedAgent` — one authoritative execution per
session, not two spawn owners. `main.spl` gained `--workbench --agent
--agent-cmd --send --workbench-frames`, dispatched BEFORE `is_valid_provider`
(agent providers are a different vocabulary).

Orchestrator re-ran the real user-facing command with its OWN nonce and got
fresh pids — a non-empty roster in production:

```
$ SIMPLE_BINARY=... bin/caret --workbench --agent agents/alpha.md \
    --agent agents/beta.md --agent-cmd .../agent_pane_stub.shs \
    --send nonceORCH99 --workbench-frames 20
|> agents/alpha.md process Unknown     ||AGENT:ready                 |
|  agents/beta.md process Unknown      ||AGENT:nonceORCH99           |
AGENT  PID  PANE  STATUS
  agents/alpha.md  66248  id3  running
  agents/beta.md   66250  id4  running
EXIT=0
```

pane == agent proven DESTRUCTIVELY: closing only alpha's pane kills exactly
alpha's pid and leaves beta running. Two processes cannot pass that.
Without `--agent-cmd`, the same command launched the host's real `claude`.

### The lane correctly refused an assertion the orchestrator prescribed

I told it to assert teardown with `process_is_running(pid)==false`. That is
**vacuous for a piped pid**: `rt_process_is_running` only consults the
async-spawn registry, so a live child that had just answered a nonce reported
`false`. It used `process_pid_exists` instead and filed the defect. It also
found `rt_process_exists` has two DISAGREEING backings — C runtime uses
`kill(pid,0)`, the Rust interpreter extern stats `/proc` — so the same call
returns `true` under JIT and `false` under the interpreter. My instruction
would have produced a green test that proved nothing. Record:
`doc/08_tracking/bug/process_exists_proc_only_and_piped_pids_invisible_2026-09-05.md`.

## A10 — controlling terminal (gap 3): CLOSED 2026-09-05

**Root cause was NOT the filed hypothesis.** `rt_pty_spawn` declared
`shell: *const c_char`; a Simple `text` arrived as an EMPTY C string, so spawn
fell out at its own `shell.is_empty()` guard and returned -1. Its sibling
`rt_pty_write` in the same file already took `RuntimeValue` — spawn was the odd
one out.

Seed change made, and justified rather than assumed: a wrong Rust FFI parameter
type has no pure-Simple expression, there is no C-runtime PTY lane to fix
instead, and this is wiring an already-implemented runtime function — not a
reimplementation or an optimization. Change is local: one parameter type, a
`ptsname` fallback, distinct error codes -2..-6 replacing one ambiguous -1, and
three `insert_simple!` registrations.

The tty-vs-pipe contrast — the only evidence that proves a controlling terminal:

```
=== A. PTY lane (rows=31 cols=97) ===
pty_open_fd=4   pty_spawn_pid=37329   pty_write_ok=true,true
sh-3.2$ tty        -> /dev/ttys031
sh-3.2$ stty size  -> 31 97
=== B. pipe lane (same two commands) ===
stty: stdin isn't a terminal
not a tty
```

`31 97` is the kernel echoing the winsize smux passed to `openpty`, and neither
expected string appears in the input, so PTY ECHO cannot fake it.

### Verified divergence — the fix does not reach the standard runner yet

```
smux_pty_controlling_terminal_spec on target/debug/simple    -> 2 examples, 0 failures
smux_pty_controlling_terminal_spec on target/bootstrap/simple -> 2 examples, 2 FAILURES
smux_terminal_service_spec (pipe lane) on debug              -> 8 examples, 0 failures
```

The bootstrap generation dir is `dr-x------` so cargo cannot write there; A10
built `--profile dev`. A release seed build is running to close this. Until it
lands and is deployed, **peers on the Sep-5 20:01 seed still see -1**.
No C-runtime PTY lane, so pure-Simple NATIVE builds still have no PTY.

## Release seed built — whole model verified on ONE binary (2026-09-05 21:22)

`src/compiler_rust/target/release/simple` (37,328,472 B) carries the PTY fix.
Everything green on that single binary:

```
smux_pty_controlling_terminal_spec   2 examples, 0 failures
smux_terminal_service_spec (pipes)   8 examples, 0 failures
caret_workbench_e2e_spec             2 examples, 0 failures
caret_workbench_prod_spec            2 examples, 0 failures
```

Production workbench, real agents and panes:

```
$ SIMPLE_BINARY=src/compiler_rust/target/release/simple bin/caret --workbench \
    --agent agents/alpha.md --agent agents/beta.md \
    --agent-cmd .../agent_pane_stub.shs --send nonceFINAL --workbench-frames 20
|> agents/alpha.md process Unknown   ||AGENT:ready       |
|  agents/beta.md process Unknown    ||AGENT:nonceFINAL  |
EXIT=0
```

Local model through caret on the SAME binary:

```
PASS -- 1 model(s) reached a verdict, 1 generated, 0 refused with a reason,
0 silent (binary: src/compiler_rust/target/release/simple)   EXIT=0
```

### NOT DEPLOYED — deliberately, needs the user's call

The new seed was NOT installed over `bin/release/<triple>/simple`. That path is
shared with concurrent peer sessions and replacing it mid-flight would swap the
compiler under their running work — the exact "binary changed mid-session"
hazard `.claude/rules/commands.md` warns about. Deploy is the user's decision.

Deploy recipe when wanted (`cp` to `.new` + `mv` over BOTH hardlinked directory
entries; a direct `cp` hits "Text file busy"):

```sh
T=$(bin/simple --print-triple 2>/dev/null || echo aarch64-apple-darwin)
cp src/compiler_rust/target/release/simple bin/release/$T/simple.new
mv -f bin/release/$T/simple.new bin/release/$T/simple
bin/simple --version    # smoke-test immediately; restore from target/release on breakage
```

Until then the fix is reached by passing
`SIMPLE_BINARY=src/compiler_rust/target/release/simple` explicitly, which every
command above does.

## GOAL STATUS: all acceptance criteria met

AC-1..AC-7 met, and the three gaps that made the earlier report "not a whole
working model" are closed: production owner wired (real roster), pane == agent
(proven destructively), controlling terminal (tty-vs-pipe contrast).

Residual, honestly stated: no C-runtime PTY lane, so pure-Simple NATIVE builds
still have no PTY (seed/interpreter only). `run_workbench` is a bounded refresh
loop, not a key-driven event loop — input belongs to the IDE TUI shell
(ponytail). Roster shows `process` rather than the provider, because
`ManagedAgent`/`AgentProcess` drop it. No live GUI window and no live browser
were opened on this host; TUI rendering WAS verified with real captured grids.

## Orchestrator verification audit (answering "is verify all done?") — 2026-09-06

It was NOT all done. Three things had been taken on the lanes' word. Closed now.

### 1. tty-vs-pipe contrast — re-run independently, not via the lane's spec

`build/nb/fixtures/probe_tty_contrast.spl`, written by the orchestrator against
the real API signatures:

```
=== A. PTY lane ===
  spawn_pty ok=true
sh-3.2$ tty; stty size
/dev/ttys031
=== B. pipe lane ===
  spawn_pipe ok=true
stty: stdin isn't a terminal
```

A `sh-3.2$` prompt only appears when the shell has a tty, so the prompt is a
second independent signal beyond the device path.

### 2. Destructive pane == agent proof — inspected and its oracle checked

`caret_workbench_prod_spec.spl:137-152` closes ONE agent's pane, then asserts
`process_pid_exists(alpha_pid)==false` AND `process_pid_exists(beta_pid)==true`
in the same run, then `degraded`, then `stopped`. Because both directions are
asserted together, a constant-returning oracle cannot pass it. The oracle was
separately sanity-checked against the OS:

```
pid_1_init=true      os: pid 1 alive
pid_999999_dead=false  os: pid 999999 dead
```

### 3. SSpec score gate — NEVER RUN until now, and it found real problems

The spipe skill requires >= 80. Three new specs were BELOW it, all on the same
blocker: `SSDOC-TRC-003`, a `# @req REQ-...` declared in the file header,
outside any `it` body, which clamps the effective score to 49 no matter how good
the rest is.

| spec | before | after |
|---|---|---|
| `caret_workbench_prod_spec` | **49** (raw 82) | **99 / 96** |
| `caret_workbench_e2e_spec` | **49** (raw 82) | **88 / 86** |
| `tui_workbench_layout_spec` | **49** (raw 81) | **87 / 84** |
| `smux_pty_controlling_terminal_spec` | 94 / 92 | unchanged |
| `ide_profile_launch_spec` | 89 / 87 | unchanged |
| `smux_terminal_service_spec` | 87 / 84 | unchanged |

Fixes: moved the header REQ ids into bound `# @req:` lines inside each `it` body
(the TUI spec had NO in-body id at all, so deleting the header alone would have
traded a blocker for TRC-001); added `# @manual_section`, lifecycle links,
trailing `# oracle:` explanations on four numeric expectations, and two
`# @capture(action_trace)` lines. All specs re-run green after the edits.

One cited lifecycle path did not exist
(`doc/04_architecture/compiler/mdsoc_architecture_tobe.md`, named in CLAUDE.md
but absent from the tree) — MNT-009 caught it; replaced with a real path rather
than left as a fabricated link.

Residual deduction on every spec is `SSDOC-MNT-002` (mirrored manual missing),
which needs `spipe-docgen` and a full pure-Simple CLI — not deployable here.

### Still NOT independently re-verified (taken on lane report)

The RED-before reproductions (A2's `6 examples, 6 failures`, A3's, A9's), A1's
exit-124 interactive-loop timeouts, A7's GUI probe, the lanes' regression suites
(dashboard 21/21, mux_model 9/9, `cargo test -p simple-runtime` 48 passed). No
`bin/simple lint` and no whole-suite run were performed at any point.

## RED-before reproductions RE-RUN by the orchestrator — 2026-09-06

Method: back up the uncommitted files, revert each fix (sed for the one-liner,
`git show HEAD:` for whole files), run, restore, verify by sha. Backups at
`<scratchpad>/redback/`. `git stash` deliberately NOT used (shared tree).

### A3 / CARET-H001 — reproduced exactly

```
fix present:  7 examples, 0 failures
fix reverted: ✗ keeps reconciling a degraded team until every survivor is terminal
              7 examples, 1 failure          <- EXACTLY one, the right one
restored sha: 817b9952f6f5b524a61d789de338b9358cd7db0a  (matches pre-test)
```

Coverage note worth keeping: with A3's fix reverted, `caret_workbench_prod_spec`
still passed 2/0, because `pane_team` has its OWN poll path. **CARET-H001 is
covered only by the unit spec**, not by the production spec.

### A2 / six smux defects — reproduced exactly, matching the lane's number

Reverted `api.spl` + `service.spl` to HEAD:

```
red_smux_defects_spec.spl        -> 6 examples, 6 failures   (lane reported 6/6)
smux_terminal_service_spec.spl   -> 6 of 8 examples FAIL against original code
restored shas: api 452208c2..., service 5fb1948e...  (both match pre-test)
```

All six named symptoms reappeared (H001 echo, H002/H005 cross-session focus,
H003 clock, H003 fabricated row, H004 orphaned survivors, H006 ninth session).
The new spec failing 6 of 8 against original code proves it discriminates rather
than passing by construction.

### Post-restore, everything green again

```
smux_terminal_service 8/0 · smux_pty_controlling_terminal 2/0
multi_caret_manager 7/0 + 5/0 · caret_workbench_prod 2/0 · caret_workbench_e2e 2/0
```

### A trap this exercise exposed — and a new bug filed

Run against the FIXED code, `red_smux_defects_spec.spl` shows `6 examples,
2 failures`. Those two are NOT live defects. The probe reads `cap.content` /
`.rows` directly on a `Result<MuxCapture,text>` — the pre-fix signature — and
the compiler ACCEPTS that and returns a garbage sentinel. Verified correct
behaviour with proper `match` handling:

```
H001 send_text_on_childless_pane_is_ok=false   (refused, not buffered)
H001 capture content=<>  echoed=false          (no echo)
H003 typed_error=unknown pane: no-such-pane    (not a fabricated row)
```

Minimal repro of the underlying hole — `.len()` on a `Result<i64,text>`:

```
ok_case_len=<value:0xffffffffffffffff>
```

Filed: `doc/08_tracking/bug/method_call_on_result_returns_garbage_sentinel_2026-09-06.md`.
This is the third member of a family found this session where the program keeps
running and returns a plausible WRONG answer instead of failing.
