# SMUX Windows ConPTY live workflows

**Status: authored manual; generation and execution pending (TEST_BLOCKED).**
Source: `test/03_system/tools/smux_windows_conpty_features_spec.spl`.
Native Windows and an admitted general pure-Simple SSpec runner are required.
This document describes expected outcomes; no child transcript or PASS exists.
SPipe docgen, zero-stub validation and maintenance scan remain pending.

## Child output — REQ-SMUX-WIN-001

1. Create a session and spawn `cmd.exe /d /q` through production ConPTY support.
   The spawn returns a positive process ID and the child reports alive.
2. Set a variable to `READY`, then echo a prefix plus the variable expansion.
   Capture must contain the expanded `SMUX_OUTPUT_READY` token, which was
   absent from the command input. Echoing input alone cannot satisfy it.
3. Close the PTY; the child must no longer report alive.

## Background execution and reattach — REQ-SMUX-WIN-001

1. Start a shell, attach a client and set child state to `SURVIVED`.
2. Submit a delayed command and detach the last client. Poll capture while no
   clients are attached; the child must produce `SMUX_DETACHED_SURVIVED`.
3. Reattach from a new client and confirm the same pane ID remains. A fresh
   command must expand the preserved child variable to `SMUX_RETURN_SURVIVED`.
4. Close the PTY.

## Independent live panes and refusal — REQ-SMUX-WIN-001

1. Split the window and start an independent Windows shell in each pane.
   A second spawn into an occupied pane must fail.
2. Set the same variable to `ALPHA` in one shell and `BETA` in the other.
   Each capture must contain its own expanded marker and exclude its sibling's.
3. Select stacked panes on a new service canvas. Both children remain alive;
   fresh commands expand each child's original variable value independently.
   This proves child survival only after execution, not child resize delivery.
4. Close the first PTY. The sibling must remain alive until explicitly closed.

Every output wait has at most five seconds of polling sleeps plus capture and
runner work; missing output fails an assertion. The detached scenario actively
polls/drains capture and cannot prove unattended owner progress without polling.
Wrong-host execution also fails explicitly. There are three authored
scenarios, none executed. These checks do not prove independent screen clients,
daemon persistence, terminal resize delivery, rendered frames or full tmux
parity. See `doc/03_plan/sys_test/smux_windows_phase3_features.md` for gates.
