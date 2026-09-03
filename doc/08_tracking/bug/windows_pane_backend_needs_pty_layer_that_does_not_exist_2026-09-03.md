# Windows pane backend is stubbed — the repo has no PTY layer to build it on

Filed 2026-09-03. Status: OPEN (gap, not a regression).

## What is stubbed

`src/app/llm_caret/pane_backend.spl` backs the `cs` caret suite. On POSIX it
drives tmux (`list-panes`, `select-pane`, `resize-pane -Z`, `send-keys -l`,
`kill-pane`) through the sosix facade. On Windows `pane_backend_name()` returns
`"windows"`, `pane_available()` is hard-false, `pane_list` returns `[]`, and the
mutating operations return `false`.

Nothing is fabricated: there is no invented pane list, and no operation reports
success it did not perform. That is deliberate — a plausible-looking fake pane
roster is worse than an honest refusal.

## Why it is stubbed, measured rather than assumed

tmux does not exist on Windows, so the backend needs a pseudo-console. Scanned
the tree on 2026-09-03:

- `rt_pty_*` / `openpty` externs anywhere under `src/lib/`: **zero**.
- `ConPTY` / `CreatePseudoConsole` in repo source: **zero**. The only matches are
  inside vendored Windows import libraries
  (`src/compiler_rust/vendor/windows_*/lib/windows.0.5x.0.lib`), i.e. binary
  blobs, not code that calls them.

So the repo has **no pseudo-terminal support on any platform**, Windows or
POSIX. On POSIX that has never mattered because tmux owns the ptys.

## Consequence

"Windows panes" is not a backend-shaped task. It requires, in order:

1. a PTY capability in the runtime (ConPTY on Windows: `CreatePseudoConsole`,
   pipe plumbing, resize, teardown);
2. a Simple-side facade for it, which belongs behind sosix per
   `doc/02_requirements/nfr/cs_caret_suite.md` NFR-1;
3. a pane/session model that `cs` can drive — effectively an in-process
   multiplexer, since there is no tmux to delegate to;
4. only then the `pane_backend` Windows arm.

Steps 1-3 are each larger than the entire POSIX pane backend, which is a thin
argv builder over an existing multiplexer.

## What was considered and rejected

**Building it on sosix.** `src/os/sosix/` is SimpleOS-internal: `process.spl`
goes through `os.userlib.syscall_raw.syscall` and imports `os.kernel.errno`.
`sosix/host/` is display-surface, input-stream and library-capability adapters
for SimpleOS on a host — not a process/terminal layer, and it has no Windows
backend. Building the Windows pane backend "on sosix" would mean writing a
sosix Windows host backend first, which is strictly more work than writing the
pane backend directly, plus a capability layer.

**A `variants/` overlay for the platform seam.** Rejected for now: an overlay
selects between real implementations, and there is currently only one real
implementation plus a stub. Promotion is mechanical once a Windows arm exists.

## Interim behaviour

`cs` itself runs on Windows — `bin/cs.cmd` delegates to `bin\simple.cmd cs`, and
the dashboard, harness grammar, provider dispatch and command handling are all
platform-neutral. What Windows loses is pane switching, maximize, and delivering
a chat message into an agent pane, because all four are tmux operations.

## Not claimed here

That a pure-Simple ConPTY binding is infeasible. It is ordinary work; it simply
has not been started, and nothing in this lane depends on pretending otherwise.
