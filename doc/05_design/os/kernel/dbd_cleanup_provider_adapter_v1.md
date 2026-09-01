# DBD cleanup provider adapter v1

Status: implemented as an unwired prerequisite; unverified.

## Boundary and ownership

The module singleton is the sole mutable provider owner. It retains the generic
cleanup-fence authority, 64 bounded persistence-owner identities, 64 bounded
transaction rows, current attempts,
cancellation evidence, and partial results. Public values are opaque copied
handles/commands or non-authorizing receipts. The DBD worker domain receives
one command at a time and returns an encoded boolean plus at most 128 bytes of
evidence; it never receives mutable owner state.

Every command is bound to the exact task ID, lifecycle generation, cleanup
transaction ID/generation, attempt ordinal, row generation/nonce, and command
nonce. Each command also carries the owner-issued opaque persistence identity
and generation; the executor must resolve that capability through the same
non-rebinding DBD owner registry. Duplicate live cleanup identities and conflicting result replays fail
closed. Lookup and replay validation are O(1); admission is a bounded O(64)
scan and retains no work-proportional allocation.

## Side-effect order and retry

The provider issues two idempotent actions in order:

1. sync the canonical DBD journal and its namespace durability boundary;
2. close the quarantined persistence owner without discarding an ambiguous
   handle.

Only the first accepted result for a command nonce changes owner state. An
exact replay returns the retained receipt. A failure stays `RetainedPartial`
and reissues only the missing action. Successful journal sync therefore is not
repeated when close needs retry.

Cancellation is merely a request while a command remains active. The adapter
accepts the provider's quiescence acknowledgment only after that command has
returned. A retry consumes the exact generic-fence ACK, rotates the underlying
attempt identity, invalidates copied old commands, and preserves completed
substeps. Completion is reported only after both substeps and the generic
fence's completion/finish transitions succeed.

## Explicit exclusions

This adapter does not call filesystem syscalls itself, copy a value-semantic
`DbdDbfsAdapter`, publish Scheduler `Zombie`, or claim that a timeout proves
quiescence. The future DBD executor must map `JournalSync` to the canonical
durable journal operation and `QuarantineClose` to its retained persistence
owner. Scheduler integration must consume the terminal authenticated receipt;
an indeterminate receipt is never terminal cleanup authority.

Static behavioral coverage is in
`test/01_unit/os/kernel/scheduler/dbd_cleanup_provider_adapter_v1_spec.spl`.
