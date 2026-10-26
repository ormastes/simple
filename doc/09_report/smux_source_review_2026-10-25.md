# SMUX geometry and notification source review

Date: 2026-10-25. Base: `1e431722b40236eda5e80bd5f5bf06395b0d0d08`.
Scope: frozen geometry, rollback, session targeting and notification changes.
**Source review only; compiler, native runtime and SSpec execution NOT_RUN.**

No remaining concrete P0/P1/P2 finding was identified in the reviewed delta.
This is not production admission or completion of the planned SMUX feature suite.

The initial P2 split-rollback finding is addressed: the service checkpoint
restores the original manual reference canvas instead of reanchoring rounded
rectangles. It validates current geometry and child identities, refuses a new
child in the added pane, preserves current surviving pane owners, and is consumed
after successful restoration. Both interactive and remote spawn-failure callers
use this transaction. The authored regression covers 80 → 40 → split → rollback
→ 80 columns and requires the original 39-cell width, plus stale-checkpoint and
repeat-rollback refusal. The obsolete `layout tiled` expectation for a manual
`current` request was corrected to `layout manual`.

No additional concrete finding was identified in the bounded notification queue,
attachment-scoped routing, oldest-only acknowledgement, lifecycle clearing,
control-safe cell clipping, or console-write-before-acknowledgement integration.
Shared-token authority and the absence of attachment expiry remain explicit
limitations. No actual console delivery, PTY resize, child execution or test
success is claimed. Future lifecycle/architecture changes require their own review.

## Reviewed input SHA-256 values

These pins identify the earlier geometry/notification review snapshot, before
the separately reviewed lifecycle and lease integration. They must not be used
as final hashes for files changed afterward. Final lease inputs are retained in
`smux_source_review_2026-10-25.sdn` beside this report.

Paths are relative to `src/os/apps/smux/`, except the explicitly named tests.

| Input | SHA-256 |
|---|---|
| `split_checkpoint.spl` | `0589df39965f31a5f5d58f87e61e29aed55ecb322b7a89396678bcd1a066cdf9` |
| `api.spl` | `37a20623c1c41958d81a21dbc3a44da18c987bb790b66dbe07c512ce4dfd253b` |
| `interactive_protocol.spl` | `09d08b88da11e35552e4b832eb9330be2107690667835bbab7a08cdc710f5fcc` |
| `smux_remote.spl` | `40f2fd4e761f81f0f920b7093974d0b55f69d60367df24ee6f0640b7de78f63d` |
| `client_notifications.spl` | `d586d0738544557a201a22ee94539ac6bd144bd73084a7206584e1728e0ed192` |
| `notification_protocol.spl` | `f181fefb2e0f80829a43591ea459e272d421401561db1da24d361f7c87c34708` |
| `notification_client.spl` | `49b1ac69eedb5137038f519f5daae8cbe91816885140514dffabe5122c5f09f7` |
| `test/03_system/tools/smux_service_layouts_spec.spl` | `deb904d2d43d5ee4d84e453c1cec75dedd57cf048c6f732d67b4f62550deb290` |
| `test/03_system/tools/smux_interactive_protocol_spec.spl` | `e0716f5293c1a07a8deef63eaac8aa3ba09d29f3eeecd7b1b5b231109e1549d2` |
| `test/03_system/tools/smux_session_messaging_spec.spl` | `83d8f7dad7375034c31bd7303a18c0ab6ea7ff447e1de211f78f229eae28177d` |

Detailed review history is retained locally at
`build/review/astra-smux-source-review.md`. No previously passing execution check
was rerun for this review.

## Subsequent lifecycle and lease review

Independent source review found no concrete P0/P1/P2 in the targeted session
rename/checked partial-cleanup kill changes, or the managed lease integration.
The five reviewed lifecycle functions remained byte-identical during the lease
review. Checked entropy, monotonic expiry, secure owner incarnation, stale-token
refusal and canonical session identity are present. Each post-admission
interactive command is validated before dispatch; the finite whitelist excludes
recursive envelopes and administrative commands, and rejects cross-session or
mismatched inner-client targets. Notice polling and acknowledgment use the same
current lease, so a superseded client cannot consume a replacement's notices
through the interactive path. Legacy owner-admin authority remains explicit.

Nine lifecycle and nine lease scenarios are authored. They have not run. Actual
client-kill recovery, heartbeat/sweep timing, provider/clock failure injection,
native cleanup and all Phase3 compilation remain unverified. This review does
not admit N2, a complete CoreMux backend, or all Caret tmux workflows.

## Static checkpoint

Working and staged direct-environment/process ownership audits passed.
Staged whitespace validation passed after removing one extra blank line at the
end of client_notifications.spl; that formatting-only change follows the earlier
notification review and is pinned in the accompanying SDN. The executable-spec
layout scan returned zero files under doc/06_spec. These checks do not execute
Simple source and are not a compiler, SSpec or production PASS.

Unrelated image materialization differences and separately modified persistence
acceptance files in the shared worktree are excluded from this checkpoint.
