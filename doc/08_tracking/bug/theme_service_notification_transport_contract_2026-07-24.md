# Theme Service Notification Transport Contract Is Missing

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Scope

`src/os/services/theme/theme_service.spl` claims that a successful theme
change notifies subscribed compositor and GUI clients. The service currently
stores subscribers as bare `u64` IPC port identifiers, but `_notify_all()` is
only a `pass_dn` placeholder.

## Confirmed root cause

The kernel IPC API exposes delivery through
`IpcOutputPort.send_fn(IpcMessage)`. `ThemeService` does not own an
`IpcOutputPort`, an injected send callback, a source port, or a specified
theme-change method/payload schema. A `u64` destination alone cannot deliver
an event.

The missing contract includes:

- the source port used by the theme service;
- the theme-change IPC method identifier;
- whether delivery is synchronous or asynchronous;
- the payload representation for canonical theme id, source fingerprint, and
  revision;
- send-failure and stale-subscriber behavior;
- construction/wiring of the production `IpcOutputPort`.

## Why implementation stopped

Adding an in-memory counter or queue would make unit tests observable without
notifying the subscribed IPC ports. Replacing `[u64]` with callbacks would
silently change the documented IPC protocol. Constructing an `IpcMessage`
inside the service without an output port would add a second, unwired
transport path.

All three would invent an ABI and could report a successful theme change while
the compositor continues rendering the prior snapshot.

## Required design decision

Choose and document one production transport:

1. Inject an `IpcOutputPort` (or a narrow `fn(IpcMessage) -> i64` adapter) when
   constructing `ThemeService`, retaining numeric subscriber ports; or
2. replace the IPC subscription protocol with typed in-process callbacks and
   update all service ownership/lifetime rules.

For option 1, define a versioned `ThemeChanged` message whose durable fields
are canonical theme id, source manifest fingerprint, material fingerprint,
and monotonic service revision. The change operation must:

1. resolve/load one `ResolvedThemePackage`;
2. install `pkg.snapshot` through
   `apply_theme_render_snapshot_to_wm_chrome`;
3. update active id/tokens/snapshot and increment revision exactly once;
4. notify every registered port with that same revision;
5. return or retain delivery failures without rolling the installed snapshot
   back silently.

## Acceptance gate

`test/01_unit/os/services/theme_service_notification_contract_spec.spl`
remains fail-fast until the transport contract and production wiring exist.
It must then be replaced by behavioral tests proving:

- aliases resolve to the canonical package id;
- WM chrome observes the exact immutable snapshot;
- one successful change increments revision once;
- every subscriber observes that revision and theme identity;
- an invalid/unloadable package changes neither snapshot nor revision;
- delivery failure is explicit and testable.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
