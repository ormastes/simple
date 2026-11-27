# caret broadcast skips a private-session pane when run inside another tmux (2026-11-14)

Status: FIXED (branch work/smux-caret-live-fixes-20261114)

## Symptom
`test/01_unit/app/llm_caret/agent_workspace_spec.spl` "broadcasts one command
to every pane" fails `expected 1 to equal 2` (+ marker never seen) when the
test runs inside a tmux pane; passes with `env -u TMUX -u TMUX_PANE`.

## Reproducer
From inside any tmux pane (`TMUX_PANE=%0`):
`bin/simple test test/01_unit/app/llm_caret/agent_workspace_spec.spl`.
Spec step: "The same pane id on ANOTHER tmux server names no pane of this
workspace" in "never broadcasts into the pane it is running from".

## Root cause
`_own_pane_id()` (`src/app/llm_caret/agent_workspace.spl`) returned
`TMUX_PANE` unconditionally. tmux pane ids are numbered per server; the
workspace runs its own `tmux -L <socket>` server whose first pane is also `%0`,
so `send_to_each_pane` excluded it as "own pane".

## Fix
`_own_pane_id(ws)` honours `TMUX_PANE` only when the socket path in `$TMUX`
(`<path>,<pid>,<session>`) ends in the workspace's `ws.socket`. The own-pane
spec now sets `TMUX` as tmux does (faithful simulation) and asserts both the
skip (same server) and no skip (foreign server).

## BSD
Same tmux semantics on FreeBSD; the fix applies identically.
