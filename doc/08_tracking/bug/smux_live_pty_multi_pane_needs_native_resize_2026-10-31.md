# smux cannot split or zoom next to a live PTY child without a native resize provider

- **Filed:** 2026-10-31
- **Status:** OPEN (capability absent, fail-closed by design)
- **Lane:** Windows caret triage, Rust seed `simple test`
- **Keeps RED:** `test/01_unit/app/llm_caret/pane_backend_spec.spl`, "spawns a shell, runs a typed command in it, then maximizes and kills it"

## Evidence

- `src/lib/sys/pty.spl:94` `can_resize()` returns `false`: the source-tree runtime
  ABI has no resize operation (the seed registers only `rt_pty_open/spawn/read/write/close/is_running`).
- `src/os/apps/smux/window_layout_service.spl:248` then refuses to resize any pane
  holding a PTY. Probe: after `pane_spawn` of one `cmd.exe`, `smux_split_pane`
  answers `terminal layout requires native resize capability`.
- `src/app/llm_caret/pane_backend.spl:299-301` turns that into an empty `Pane`, so
  the second `pane_spawn` returns `pane_id=""`, `pid=0`, and the reason is dropped.
- The refusal is not Windows-specific in the source: `can_resize()` is
  unconditional in this module. Not run on a POSIX host here.

## Why the spec changed but stays RED

The old spec zoomed a lone pane and expected `zoomed`. A lone pane stays unzoomed
by contract (`window_layout_service.spl:475`, tmux parity, pinned by
`test/03_system/tools/smux_zoom_spec.spl:112`), so that premise was wrong on every
host. The spec now asserts the lone-pane no-op (passes) and maximizes with a real
sibling pane, which needs this capability. Those sibling steps have never been
observed green.

## Unblock

Compose a native PTY provider whose `can_resize()` is true (ConPTY
`ResizePseudoConsole` / `TIOCSWINSZ`) into the source-tree runtime, then re-run the
spec. Separately worth doing: return the split error from `_smux_free_pane` rather
than an empty pane.
