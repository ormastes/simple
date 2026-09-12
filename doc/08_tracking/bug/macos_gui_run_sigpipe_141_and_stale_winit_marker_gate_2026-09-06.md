# macos-gui-run.shs exits 141 after a successful launch; its winit-marker gate refuses dlopen-route binaries

**Status:** RESOLVED 2026-09-12 (see the RESOLVED section at the end)

**Date:** 2026-09-06 · **Status:** OPEN · **Found by:** slim-UI lane A07 (G1 presentation), read-only scope — not patched

## Defect 1 — SIGPIPE 141 after `open` succeeded

`scripts/gui/macos-gui-run.shs` runs under `set -o pipefail`; its own `ps | awk` pid
lookup gets SIGPIPE, so the script exits **141** *after* `open -n` already launched the
bundle, and no PID receipt is written. Callers that read the exit status see a failure
for a run whose window is on screen. `scripts/check/check-ui-slim-gui-present.shs`
works around it by recovering the bundle path from the `launching …` line.

## Defect 2 — `has_winit_marker` is stale for the dlopen route

The launcher selects a binary by grepping it for `rt_winit_event_loop_new`. Since the
GUI route loads `libspl_winit.dylib` through `GuiRenderer` at runtime, a current seed
without baked `rt_winit_*` symbols would work but is refused; only the 2026-07-25
`bin/release/aarch64-apple-darwin/simple` carries the marker. Same anti-pattern as
`.claude/skills/spipe.md` § "Grepping a BINARY for a symbol … fails closed": probe
capability by calling it.

## Also required to run at all

`open -n` starts the app with cwd `/` and does not forward `SIMPLE_SPL_WINIT_PATH`, so
`GuiRenderer`'s relative `build/sffi/libspl_winit.<ext>` candidate never resolves. The
check exports `DYLD_LIBRARY_PATH=<repo>/build/sffi` and copies the prebuilt dylib there.

## Unblock

Fix the pid lookup (read `ps` into a variable, or `|| true` the awk stage) and replace
the marker grep with a positive probe (run the candidate with a `--probe-winit` that
attempts the dlopen). Add a spec that launches through the script and asserts exit 0
plus a PID receipt when a window was created. Evidence of the working run:
`doc/07_guide/ui/ui_slim_gui_presentation.md`.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).

## RESOLVED 2026-09-12 (Lane 4)

Both defects fixed in `scripts/gui/macos-gui-run.shs`; measured on Apple M4.

**Defect 1 — SIGPIPE 141.** `find_exact_app_pid` captured `ps -axo pid=,command=`
into a variable first (status read on the next line, never through a pipeline),
and the awk stage no longer `exit`s early — the first match is latched and
printed at `END`, so no consumer ever hands the producer a closed pipe. `|| true`
on the awk stage was deliberately NOT used: it would mask a real failure.

**Defect 2 — stale winit marker.** `has_winit_marker` now admits a candidate when
either the binary carries the baked `rt_winit_event_loop_new` /
`window_winitmodule.smf` symbols **or** `libspl_winit.<ext>` is resolvable on the
path `GuiRenderer` searches (`SIMPLE_SPL_WINIT_PATH`, then `DYLD_LIBRARY_PATH`
entries, then `<repo>/build/sffi`) — the dlopen route the bug describes. Stated
honestly: this is a capability-PRESENCE probe, not a call probe; it proves the
dylib is on the search path, not that `dlopen` will succeed. Strict-evidence mode
keeps the old behaviour via a separate `has_baked_winit_marker`, because the
admitted driver there is hash-pinned and a runtime dlopen is outside that hash.

**Evidence.** `test/01_unit/scripts/macos_gui_run_pid_lookup_contract_test.shs`
extracts each function VERBATIM from the tracked launcher and runs it under the
same `set -euo pipefail`, against a fake `ps` that writes 20001 lines with the
match first:

```
EXTRACT_PID_OK=YES
PID_RC=0 PID=4242
SABOTAGE_RC=141        <- the exact pre-fix `ps | awk '...exit'` shape
EXTRACT_WINIT_OK=YES
WITHOUT_DYLIB=NO       <- refused with no libspl_winit anywhere
WITH_DYLIB=YES         <- admitted once build/sffi/libspl_winit.dylib exists
BAKED=NO               <- strict probe still refuses the marker-free file
CONTRACT=PASS
```

Specs (reproduce + generalize):
`test/01_unit/scripts/macos_gui_run_pid_lookup_spec.spl` — 3/3 PASS.
