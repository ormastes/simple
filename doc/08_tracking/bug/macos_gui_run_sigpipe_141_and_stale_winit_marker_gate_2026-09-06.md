# macos-gui-run.shs exits 141 after a successful launch; its winit-marker gate refuses dlopen-route binaries

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
