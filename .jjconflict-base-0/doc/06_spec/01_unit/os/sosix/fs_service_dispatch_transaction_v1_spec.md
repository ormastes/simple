# SOSIX FS v1 service dispatch transaction

The transaction accepts only a previously validated service plan, an
authoritative service buffer registry, and a positioned VFS backend. It has no
parameter through which a caller can inject buffer bytes.

## Read transaction

1. Resolve exactly one active registry entry matching the plan's owner, slot,
   generation, registration ID, and owned byte length.
2. Dispatch positioned `read_at` using a copy of those authoritative bytes.
3. Commit the returned full buffer only when dispatch succeeded and the same
   generation-bound registry entry still matches.
4. Encode the completion from the plan's operation slot, operation generation,
   request token, and API ID.

Failed, stale, ambiguous, or oversized reads return the original registry.
A zero-byte successful read (EOF) carries no partial-progress flag; only a
positive short transfer is partial progress.

## Write transaction

The backend receives only the requested slice of registry-owned bytes. A
successful or failed write returns the original registry unchanged. Completion
correlation is encoded from the accepted plan, never reconstructed from caller
fields.

## Covered scenarios

- successful READ commits bytes and emits a correlated completion;
- zero-byte EOF is not mislabeled as partial progress;
- WRITE consumes registry bytes while preserving registry content;
- stale generations are rejected before backend dispatch;
- failed and oversized READ results are never committed;
- unaccepted plans do not produce a trusted completion.
