# Hosted SOSIX completion FIFO can lose notifications after slot reuse

**Status:** Candidate fix on `feature/sosix-completion-capacity`; pure-Simple runtime verification pending.

## Evidence at `b2fb7dc979d`

`SosixHostedFs.pump` released a ring slot and ignored the result of publishing
its typed completion to `SosixCompletionQueue`. The queue is capped at 1024,
while `SosixHostedFs.create` admitted larger rings. Even with capacity one, a
caller could observe a terminal result with `poll`, release that operation,
and reuse its slot without taking the separate FIFO notification. Repeating
this filled the FIFO; later `publish` calls returned false and their
notifications were lost.

## Required invariant and candidate correction

An admitted ring has at most one unread terminal notification per slot, and
its capacity cannot exceed the FIFO capacity. Releasing an operation after
polling its result discards only that operation's unread notification. Taking
a notification clears the corresponding queued marker. The bounded discard
preserves the order of other notifications, including across FIFO wraparound.
`pump` leaves a ring completion in place if the FIFO has no room.

## Qualification

Run the hosted async and completion queue specs with a source-matched
pure-Simple binary. They cover repeated capacity-one poll/release/reuse,
out-of-order release, generation-sensitive discard, wrapped FIFO order, and
oversize ring rejection. Confirm zero rejected publications and retained
single-terminal, retirement, and sync-wait behavior. Then run the required
`src/lib` and MCP smoke gates before production promotion.
