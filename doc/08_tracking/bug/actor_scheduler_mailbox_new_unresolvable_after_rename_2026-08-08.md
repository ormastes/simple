# actor_scheduler expects the priority-mailbox API; no imported name provides it

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** High
- **Found by:** adversarial review of `a019ba19aa66` ("rename mailbox_actor.Mailbox to PriorityMailbox, resolve nogc_async_mut export ambiguity")
- **File:** `src/lib/nogc_async_mut/actor_scheduler.spl`

## The claim vs. the tree

`a019ba19aa66` renamed `mailbox_actor.Mailbox` -> `PriorityMailbox` and updated
what it treated as the sole importer (`mailbox_actor_select_spec.spl`). The
rename itself was the right call — verified, the two types are genuinely
distinct:

| | file | kind | shape |
|---|---|---|---|
| kept | `src/lib/nogc_async_mut/mailbox.spl:18` | `struct Mailbox` | bounded text-message: `capacity`, `messages: [text]`, `count`; 8 free fns, **no static `new`** — construction is `mailbox_new(capacity: i64)` |
| renamed | `src/lib/nogc_async_mut/mailbox_actor.spl:103` | `class PriorityMailbox` | off-heap priority queues: `config`, `messages`, `messages_ready`, `stats` |

## The defect

`actor_scheduler.spl` is a live consumer of the **priority** API:

```
:6-9   use mailbox.{ Mailbox, MailboxConfig, SEND_SUCCESS, SendResult }
:209   mailbox: Mailbox
:290   mailbox: Mailbox.new(MailboxConfig.default())
```

`Mailbox.new(MailboxConfig)` is unambiguously the `PriorityMailbox`
constructor shape. The `mailbox.spl` struct it actually imports has no static
`new` at all (confirmed: `grep "fn new" src/lib/nogc_async_mut/mailbox.spl` is
empty). The import was already mis-targeted before the commit, but after the
rename **no name reachable from that import provides the API this file calls**,
so the rename cements the breakage rather than surfacing it.

`actor_scheduler` is facade-exported (`__init__.spl:14-20`), so this is on the
public surface.

## Not fixed here

The fix is a judgement call the review shouldn't make unilaterally: either
`actor_scheduler` should import `PriorityMailbox` from `mailbox_actor`, or its
scheduler mailbox should be rebuilt on the bounded `mailbox.spl` struct. Both
change runtime behavior.

## Secondary findings from the same commit

- **MED — scope creep.** The commit newly exports 8 previously-unexported
  symbols (`Mailbox`, `mailbox_new` .. `mailbox_drain`, `__init__.spl:134-137`),
  beyond "resolve the ambiguity". The facade's `Mailbox` **silently changed
  identity** — priority/off-heap class -> bounded text struct. No live facade
  consumer today, so nothing breaks now.
- **MED — a third `struct Mailbox`** at `src/lib/nogc_async_mut/actors/actor.spl:254`
  in the same package. Not in `__init__.spl`, so not currently ambiguous, but the
  same latent shape that produced this bug.
- **LOW — spec verdict overclaimed.** The commit says "the spec's 5 examples still
  pass". True at example level, misleading at file level:
  `SPEC FILE VERDICT: src/lib/nogc_async_mut/test/mailbox_actor_select_spec.spl declared>=0 executed=5 passed=5 failed=0 dropped=0`
  is followed by `Files: 1 Passed: 5 Failed: 1` and rc=1. Sibling control
  `coverage_spec.spl` returns `Failed: 0`, so the file-unit FAIL is specific to
  this spec, not harness-wide. Cause unattributed (no pre-rename control run).
- **LOW — stale tracking doc.**
  `doc/08_tracking/bug/memory_superlinearity_curve_blocked_and_scoped_negative_2026-08-07.md:36`
  still asserts `export MailboxConfig, Mailbox,` at `mailbox_actor.spl:305`.

## No new ambiguity

`__init__.spl` has zero `use` lines (bare-name manifest); exactly one
`export Mailbox` remains, and `mailbox.spl:76`'s
`export use ...{MailboxConfig, SendResult, SEND_*}` predates the commit. The
stated goal — removing the double export — was achieved.
