# Caret mux/TUI N2 qualification

Selected by user: N2, 2026-10-25. These are acceptance targets, not measured results.

- NFR-CMUX-001: Run real smux and tmux core contract and Caret lifecycle suites. All mandatory requirements need matching source/producer/backend/host receipts and actual assertions. Unsupported optional cases must verify refusal without mutation; they must not be counted as successful feature execution.
- NFR-CMUX-002: On a pinned local fixture, warm p95 metadata round-trip shall be <=100ms; layout request to independently observed settled state shall be <=250ms. Record cold preparation separately and retain sample distributions, timer boundaries, RSS and fixture identities. This does not promise remote-link latency.
- NFR-CMUX-003: Complete a 24-hour background-session/reconnect soak on each qualified backend with slow consumers, event/output floods, client/server disruption, cleanup and concurrent layout conflicts. No accelerated or shortened run may be reported as the 24-hour soak.
- NFR-CMUX-004: Baseline stress fixture shall exercise at least two isolated workspace/server namespaces, two sessions per namespace, four panes and two clients per namespace. Exercise advertised session/window/pane/client limits and one-over-limit refusal separately; record actual configured limits and any shared-host resource constraints. Larger scales remain configurable, not implied by this baseline.
- NFR-CMUX-005: Queues, event buffers and captures shall have explicit byte/item bounds and observable backpressure. Record baseline/peak/settled memory, handle/process counts, dropped/refused work and pending cleanup. No unbounded retry, stdout accumulation or leaked child is acceptable.
- NFR-CMUX-006: Run crash/reconnect and stale-reference tests independently of graceful detach. A crashed client shall not permanently consume capacity or constrain surviving views. Handle generations/server identity prevent old references from addressing new objects.
- NFR-CMUX-007: Verify Unicode scalars versus UTF-8 bytes versus display cells, alternate-screen changes, resizing and zoom round-trips, cursor/control filtering and input routing against actual child/rendered state. Visual notification delivery requires successful native rendering evidence before ACK.
- NFR-CMUX-008: Failed/unsupported operations shall have explicit before/after state and commit/cleanup evidence. Tmux's lack of stronger multi-operation atomicity must remain visible, never a falsely advertised capability or a hidden partial commit.
- NFR-CMUX-009: Keep all test attempts finite, retain logs/caches and obey the six-cycle per-feature cap across sessions/worktrees. Reuse unchanged green evidence; do not rerun passed criteria without a relevant change. Missing Phase3/runtime/engine/provider prerequisites yield BLOCKED/NOT_RUN.

Status: NOT_RUN. N2 has been selected; no latency, stress, soak, memory, cleanup or backend compatibility target is currently qualified for the new interface.
