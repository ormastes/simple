# smux pane shows no stdout from `simple.exe` unless it is piped

## Status

Open 2026-11-12 (lane p1-caret). Reproduced twice on the phase-1 seed, Windows 11, smux backend.

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
