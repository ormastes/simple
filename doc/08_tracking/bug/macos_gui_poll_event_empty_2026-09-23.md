# macOS HTML GUI cannot receive editor events

Status: DRAFT / live-provider acceptance blocked. PR #1418, stacked on #1417
at `d5fc5a9b294b7a0c3ca9bcbea7b4583f9ee05eb8` for this source pass.

Integration update: #1418 carried the initial design/header/probe and was
merged into #1417. The complete implementation below now belongs to #1417.

## Reproduction and cause

`gui_shell_poll_event()` in both `src/app/editor/gui_shell.spl` and
`gui_shell_render.spl` unconditionally returned `GuiEvent(kind: "", data: "")`.
The run loops never called a provider teardown function. A working optional
HTML presentation dylib alone therefore could not deliver input or a close
request to the editor.

The initial boundary selfcheck failed to link precisely
`rt_gui_begin_session`, `rt_gui_session_present_html`, `rt_gui_poll_event`, and
`rt_gui_end_session` against #1417's original `8124a6f6304` C runtime. Its clean
rebase preserved the same missing event boundary. This reproduces the absent
runtime capability; it is not a live AppKit reproduction.

## Change

The existing lazily loaded HTML provider gains a separately versioned event
extension. Session admission requires all event symbols before displaying a
frame. Only the macOS main thread may open, present, poll, or close a session.
All loader/provider callbacks are guarded against same-thread reentry before
the initialization lock can be entered again. The process retains the dylib;
session shutdown owns release of UI state.

An atomic admission gate excludes standalone HTML calls from an active event
session and rejects session open while standalone calls are in flight. Its
reservation covers loader callbacks through shutdown. Both idle and copied
text are checked for registered-string allocation success before returning.

A 4096-byte caller buffer receives one `kind\npayload` packet; the runtime
checks length, kind, embedded NUL, and UTF-8 before copying into registered
Simple text. Idle polls reuse an interned empty string. The canonical
`nogc_sync_mut/ui/html_gui_sffi.spl` owner splits only the first newline and
both editor shell variants now open/poll/close the session.

Design and provider contract:
`doc/05_design/mac_gui_event_lifecycle_2026-09-23.md` and
`src/runtime/simple_gui_event_provider_abi_v1.h`.

## Focused evidence

Host: macOS arm64. Boundary-only C build, no AppKit/WebKit link or full
bootstrap. Commands run from the isolated worktree:

```sh
clang -c -O0 -ffunction-sections -fdata-sections -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o build/gui-event-probe/runtime.o
clang -Wl,-dead_strip -Wl,-exported_symbol,_rt_gui_begin_session -Wl,-exported_symbol,_simple_gui_test_present_hold -std=gnu11 -Isrc/runtime -Isrc/runtime/platform src/runtime/test/rt_gui_event_dynload_selfcheck.c build/gui-event-probe/runtime.o -lpthread -lm -o build/gui-event-probe/selfcheck
clang -dynamiclib -std=gnu11 -Isrc/runtime src/runtime/test/rt_gui_event_provider_fixture.c -o build/gui-event-probe/provider.dylib
clang -dynamiclib -std=gnu11 -DSIMPLE_GUI_EVENT_TEST_NO_SHUTDOWN=1 -Isrc/runtime src/runtime/test/rt_gui_event_provider_fixture.c -o build/gui-event-probe/provider-no-shutdown.dylib
```

Set `SIMPLE_GUI_HTML_PROVIDER_PATH` to the absolute fixture dylib. For each
mode set `SIMPLE_GUI_EVENT_TEST_MODE` to that mode and pass it to `selfcheck`.
The matrix used `perl -e 'alarm 5; exec @ARGV'` to bound each process.

- PASS normal: multiline text, key, focus/blur, pointer down/move/up, resize,
  idle identity reuse, close, reopen; exactly one HTML version and one event
  version call, two presentations, twelve polls, and two shutdowns.
- PASS headless and maximum 4096-byte packet.
- PASS exit 70: bad-version, poll-reject, overflow, unwritten, no-delimiter,
  empty-kind, invalid-kind, long-kind, nul, utf8, html-reentry, version-reentry,
  present-reentry, poll-reentry, shutdown-reentry, shutdown-reject,
  present-reject, thread-open, thread-poll, thread-present, thread-close,
  inactive-poll, inactive-present, inactive-close, nested, double-close, and
  missing shutdown export. Together: normal plus 29 edge cases.
- PASS `otool -L`: selfcheck links only libSystem; no eager AppKit/WebKit.
- PASS working-tree direct-env-runtime guard and whitespace check.

The final harness additionally exports `_simple_gui_test_present_hold` for a
condition-variable fixture that holds a standalone worker presentation open.
After the source review fixes, seven new focused cases PASS: valid multibyte
UTF-8, standalone-before-session (including gate release and reopen),
same-thread standalone overlap, worker standalone overlap, session open during
an in-flight standalone call, event-text OOM, and initial idle-text OOM.
The two OOM cases compile the runtime with `-Dmalloc=gui_test_malloc`; the test
wrapper refuses allocation only after successful session/frame admission.
They both exit 70 with the allocation diagnostic. A retained first event also
remains unchanged after subsequent polls and shutdown. Prior passing cases
were not rerun; cumulative focused coverage is 37 distinct modes.

An initial fixture link used `-export_dynamic`, which prevented dead stripping
of unrelated C runtime entrypoints and failed on their missing dependencies.
Exporting only the reentry probe symbol fixed the harness without changing
production code. Green checks were not rerun.

## Limits and remaining gates

The fixture is not a production WebKit provider. It proves no live rendering,
DOM input forwarding, IME/accessibility, close-drain behavior, latency/RSS, or
idle CPU target. The existing loop still renders before every poll. The 16 ms
idle wait and bounded queue are provider obligations, not runtime preemption.
Standalone HTML v1 calls must not overlap a main-thread event session.

The pure-Simple packet decoder spec is authored but not executed: no admitted
source-matched Stage-4 CLI exists in this isolated worktree. Full compiler/lib,
MCP/LSP checks, SPipe/docgen/manual evidence, live GUI tests, and full bootstrap
remain parent-owned or blocked; this is not a production verify PASS.

Astra accepted the initial design and cleared the source ownership/OOM
blockers after the atomic gate and registered-text checks. Exact-commit source
review receipt remains required at handoff. The early
draft publication bypassed local pre-push hooks once with parent authorization;
all skipped hooks remain unclaimed and remote checks remain enabled. No root
worktree or golden-file changes belong to this patch; LFS autostash `465f542`
was preserved after the initial filter-related rebase refusal.

The source-roster check against the early draft HEAD found the new event
selfcheck not yet in that commit's roster plus inherited
`test/rt_windows_file_publish_selfcheck.c`. This patch inventories both new
event C fixtures; the unrelated Windows inventory repair belongs to its own
lane. Repository-wide SFFI backlog generation passed four assertions and
reported 11063 source-only rows; it is not provider admission evidence.

## Combined #1417 integration receipt

Astra issued SOURCE PASS for `fc01b0276d5` after the two ownership/OOM fixes.
That implementation was cherry-picked without conflict onto exact remote
#1417 head `184c0835b44ad5abaa4ecab071753b1486d08e79` in a new sparse worktree,
producing `8edbf0de18d`. The extracted loader retains the newer thread-local
initialization guard, `sched_yield` lock wait, and flag reset. The outer GUI
callback guard now catches callback reentry before entering that loader;
the expected diagnostic is `GUI callback reentry` with the same exit 70.

All checks below ran once on that combined source, in
`build/gui-event-integration/`:

- Core-C UTF-8/math/array parity: **123 checks, 0 failures**.
- Event/session fixture matrix: **37 modes, 0 failures**, including both
  allocation fault modes and all three standalone/session overlap modes.
- Existing standalone HTML fixture matrix: **7 modes, 0 failures** (accepted,
  absent path, invalid path, wrong ABI, rejected frame, invalid tag, reentry).
- Direct-env runtime guard and scoped whitespace check: PASS.
- Event selfcheck dependency inspection: libSystem only; no AppKit/WebKit.
- Committed-tree executable specs under `doc/06_spec`: 0.

Five Windows script files appeared dirty immediately on this fresh sparse
checkout; they are excluded from the 13-file integration diff and were not
edited or staged. No golden changes, LFS stash, or root worktree changes were
incorporated. The same Simple/live-provider/full-bootstrap limitations above
remain; this receipt is scoped C-boundary evidence only.
