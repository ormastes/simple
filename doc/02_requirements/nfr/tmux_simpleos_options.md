<!-- codex-research -->
# NFR Requirement Options — `tmux_simpleos`

Date: 2026-04-24

## Option 1 — Developer-Usable Baseline

Description:
Prioritize a working first release over broad compatibility.

Targets:

- cold start of multiplexer service under 300 ms on hosted/dev lane
- pane input-to-visible-output median under 30 ms in local smoke scenarios
- support 4 concurrent panes in one session
- no crash on missing shell binary, bad pane target, or resize events

Pros:

- fastest path to a usable result
- easiest to verify with existing repo infrastructure

Cons:

- limited concurrency target
- no strict parity goal with upstream tmux behavior

Effort:

- `S`
- estimated files: 4-6 additional test/metrics files

## Option 2 — Interactive Strong Baseline

Description:
Treat the feature as a core OS interaction surface with stronger latency and
stability expectations.

Targets:

- cold start under 200 ms on hosted/dev lane
- pane input-to-visible-output p95 under 20 ms
- support 16 concurrent panes across multiple sessions
- detach/reattach preserves pane buffers and shell state
- no full-tree scans or per-keystroke subprocesses in hot paths

Pros:

- good long-term baseline
- forces a proper session-service design

Cons:

- more implementation and verification work
- may slow first delivery

Effort:

- `M`
- estimated files: 6-10 additional test/metrics files

## Option 3 — Upstream-Compatibility Oriented

Description:
Optimize for later stock-tmux backend compatibility and protocol fidelity.

Targets:

- stable API mapping for session/window/pane control
- explicit terminal capability and UTF-8 correctness plan
- PTY semantics documented and verified for controlling-terminal expansion
- compatibility shim for current `std.tmux` / dashboard consumers

Pros:

- best preparation for later binary-hosting experiments
- reduces migration risk

Cons:

- more architecture and conformance work before user-visible payoff
- some targets depend on OS subsystems not fully mature yet

Effort:

- `M`
- estimated files: 8-12 additional design/spec files

## Recommendation

Recommended NFR set:

- **Option 2** as the runtime baseline
- add the API-compatibility portion of **Option 3**

Reason:

- Option 1 is likely too weak for an interactive multiplexer.
- Full Option 3 is premature unless the user explicitly wants to pursue stock
  tmux binary compatibility immediately.
