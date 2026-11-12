# smux pane shows no stdout from `simple.exe` unless it is piped

## Status

Fixed, verification-pending 2026-11-12 (lane p1-caret, PR on release/1.0.0).
Opened the same day; reproduced twice on the phase-1 seed, Windows 11, smux
backend. The title's premise was wrong — see Root cause.

## Root cause (2026-11-12)

Nothing is dropped by ConPTY and the console write path is fine: a pane
running `bin/simple.exe run <print script>` captures its output (probe,
`build/probe_pane.spl`). What the piped and unpiped runs really differed in
was the SIZE of the transcript: the CLI run spews ~350 KB of seed
diagnostics (visibility/W-STR-BRACE warnings) into the pane, which `| tail`
swallowed. A pane printing 400 KB of anything (`awk` generating 2000 lines
of 200 columns, no `simple.exe` involved) reproduces it.

The owner (`src/os/apps/smux/server.spl`, serve loop) wrote ONE 4 KiB chunk
of a reply per loop turn, and every turn also polled every pane PTY through
the interpreted VT screen. With a pane ingesting a few hundred KB each turn
took tens of milliseconds, so a 400 KB `history-joined` reply (100 turns)
hit the 2 s `CLIENT_DEADLINE_MS` half-sent. The client's length frame
rejected it (`incomplete smux response`, measured: the request returned
after exactly ~2.1 s), `_smux_req` returned nil, and `capture_pane` turned
that into an EMPTY transcript. The 95 KB capture at +10 s followed by 0 at
+20 s in the timed probe is the moment the transcript crossed the size the
loop could ship inside 2 s.

## Fix

The reply path drains as much of the reply as the non-blocking socket takes
in one turn and renews the client deadline on progress (the deadline bounds
a peer that stops reading, not a long reply). Spec:
`test/01_unit/os/apps/smux/server_large_reply_drain_spec.spl` — red
`executed=1 passed=0 failed=1` with evidence `direct reply error: incomplete
smux response`, green `executed=1 passed=1`;
`agent_workspace_spec.spl` went 6/7 -> 7/7.

Still observed, not fixed here: the owner's first reply after a 400 KB burst
takes ~50 s because the VT ingest is interpreted; `capture_pane`'s 30 s
reply window then returns "" once. Pollers (`wait_for_pane_text`) tolerate
it; a single-snapshot caller does not.

## Symptom

`agent_workspace_spec.spl` example "smux: a pane never receives the broadcast
issued by the CLI running inside it" fails at
`wait_for_pane_text(ws, id + ":owner", "sent " + id + ":other.0", 120000)`.
With the evidence capture added in this lane the owner pane transcript is
EMPTY after 120 s, while the bystander pane did receive `OWN_SKIPPED` — so
the broadcast and the own-pane exclusion both worked; only the CLI's own
report never appeared in its pane.

## Reproduction (build/probe_ownpane.spl, not tracked)

Pane command `cd <wt> && bin/simple.exe run src/app/llm_caret/main.spl workspace own-smux broadcast 'echo OWN_$(echo SKIPPED)' --repo <repo>`:

| pane command tail | owner pane capture |
|---|---|
| `... --repo <repo>` (stdout is the ConPTY console) | empty |
| `... --repo <repo> 2>&1 \| tail -5` (stdout is a pipe) | `sent own-smux:main.0` / `sent own-smux:other.0` |

Same binary, same owner, same command; only whether stdout is a console
handle differs. So either `simple.exe` writes console-mode stdout through a
path the smux ConPTY screen does not record (WriteConsole on a different
handle, alternate screen, or buffered-and-never-flushed before `exec sleep`
replaces the shell), or the smux screen drops those writes.

## Not this

- Not the owner-request transient (`smux owner unavailable`) — fixed in the
  same lane (`_smux_req` retry + `smux_server_request_within`); both
  `agent_attach` calls return `ok` in the reproduction above.
- Not the broadcast exclusion — the piped run shows exactly the two foreign
  panes and never `owner.0`.

## Next step

Run `bin/simple.exe run <any script that prints>` as a pane command and
capture; then bisect between the seed's stdout path when `isatty` is true
and `smux` ConPTY screen capture. The spec example stays red (no skip) until
then.

## Follow-up 2026-11-12 (lane caret-capture): remaining workspace_recovery red

`workspace_recovery_system_spec` "starts the attach command ..." stayed red
(11/12) after PR #8582: the 302-char line never appeared within 30 s and the
pane showed only `echo EXACT_42`. Pre-existing on `origin/release/1.0.0`
`bc0ee732506` (`executed=12 passed=11 failed=1`). Bisected as this doc's next
step asked: stdout is not dropped. A pane write of the 307-char command is
accepted whole, and the owner polls fast. The shell's readline then echoes
typed input at ~0.25 s per character, so the command line takes ~75 s. Filed
separately as `smux_pane_readline_typed_input_per_char_latency_2026-11-12.md`.
The spec step now has the shell produce the 300 columns from a short command,
so it still checks capture of a wide line.
