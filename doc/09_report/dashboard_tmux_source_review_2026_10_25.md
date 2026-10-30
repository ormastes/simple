# Dashboard checked tmux source review

Independent source review, 2026-10-25. **Status: WARN.** No remaining concrete
P0/P1/P2 production defect was identified in this bounded corrected delta.
Compilation, native execution and live cleanup qualification are **NOT_RUN**:
12 authored cases, zero executed. This is not production verification PASS.

## Findings closed in source

- The original checked argv path could lose a terminal semicolon because tmux
  parses command separators after process argument delivery. The owner now
  inserts one backslash immediately before a final semicolon in every logical
  argument. tmux removes that inserted backslash, preserving the original
  argument, including any preceding backslash run. Nonterminal semicolons and
  trailing backslashes stay unchanged. This API represents one command per
  invocation. The rule matches the primary
  [tmux argument parser](https://github.com/tmux/tmux/blob/master/cmd-parse.y)
  and [manual parsing syntax](https://github.com/tmux/tmux/blob/master/tmux.1).
- Session listing previously rejected `session_attached` above one. The
  production parser now validates a nonnegative client count and maps positive
  counts to the existing attached boolean, consistent with the same manual's
  format table. The pure cases include zero, one, two, negative and malformed
  counts. The live scenario requires two real control clients and independently
  observes the count while checking the HTTP listing.
- Resize previously asserted only HTTP200. The live scenario now prepares
  neighbours on both axes and checks the actual target pane is70x20.

The live scenario also requires exact session names ending in semicolon and
backslash-semicolon, and six child `read -r`/capture oracles covering semicolons,
backslashes and UTF8. Shell-command echo cannot satisfy those standalone output
lines. These authored regressions have not run.

## Boundary review

Exact methods/routes and bounded query/body preparation precede backend access.
Canonical percent/UTF8 decoding rejects malformed octets, NUL and duplicate
decoded query keys. Mutations use flat strict JSON with duplicate decoded names,
unknown fields, invalid types and excess nesting rejected. Session separators
and control characters are refused; indexes/dimensions have explicit bounds.

Checked operations use structured arguments through an additive alias to the
existing Sosix process owner, exact session targets and explicit literal/key
input. Process calls carry10000 ms timeouts and1MiB per-stream capture caps.
Nonzero exits, at/above-cap output and truncation markers become errors rather
than partial successful snapshots. Literal/Enter partial completion is explicit.
JSON escaping may expand the response beyond the raw capture cap. Native
provider exit/drain behavior is not established by this source review.

Both mounted routing layers require a registry-backed session for mux control;
the outer HTTP route additionally checks loopback authority/origin. Static and
local-development identity strings do not bypass mux authentication. The earlier
HTTP per-read-versus-whole-request deadline limitation remains documented in the
separate authentication source review.

## Cleanup correction and execution obligations

The initial fixture treated failed `has-session` calls as absence. That source
gap is now closed: a separately owned guard session and its recorded live child
PID must remain present in a successful checked inventory while each target is
proved absent. Query failures propagate as failure/uncertain cleanup.

The fixture registers attempted session names before HTTP creation, records
initial children immediately afterward, and retains split/guard child PIDs from
creation responses. Dashboard and control processes enter a module-owned ledger
when acquired, so a helper returning Err does not lose the cleanup owner. One
outer cleanup attempts all registered processes and sessions, accumulating
errors rather than asserting after the first failed teardown. It checks target
child termination before killing the guard, then requires a successful guard
kill receipt and its recorded child's termination. Malformed/missing PID
acquisition remains failure even when best-effort teardown later succeeds.

This resolves the reviewed cleanup-proof defect in source. Live process-owner
semantics, PID observations and the cleanup branches have not executed. The
fixture coordinator must still provide private-server teardown and terminal
PID/job/quiescence receipts for crash/provider-unknown paths that prevent
in-process cleanup. Unknown cleanup remains INVALID/unqualified, never PASS.
No such receipts exist for this candidate yet.

Only scoped source inspection and a clean whitespace check were completed.

## Frozen input SHA256

| File | SHA256 |
|---|---|
| src/app/web_dashboard/tmux_api.spl | a4404de6407c3380e0d052a35a21da520b36bdb2ab1d44ac9b77d1a2d2d02495 |
| src/lib/nogc_sync_mut/tmux/mod.spl | e7ed8ad6ff663ab622c3147ec2c7c29269cc42c35a391dff9f135021dc0ce6c9 |
| src/lib/nogc_sync_mut/sosix/process.spl | ed9fbc2ade3ad98840bed730bc2b7ebec533ae9906392dd04a8fa345a2408869 |
| src/app/web_dashboard/server.spl | 1a8b830ab1a9a4fb47887c5ad8f0da38b94c045330de924f7ebb2b1e44ca31c3 |
| test/03_system/app/web_dashboard/feature/tmux_api_route_spec.spl | 1d09a1119b12163d41bca42eb196ea1dbb57977b7e158d64a9f122313b18f044 |
| doc/06_spec/03_system/app/web_dashboard/feature/tmux_api_route_spec.md | 6efaeb437ce49ef4e7ddf43fbeb4344794f40b2e98c0610f29a7cd4882888081 |
