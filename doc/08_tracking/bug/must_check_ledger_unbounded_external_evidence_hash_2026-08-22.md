# Must-check ledger permits unbounded external evidence hashing

Status: RESOLVED — `codex/session-01a023a8`

## Failure

The push ledger consumer accepts absolute evidence paths and hashes every PASS
file without a size or aggregate-byte limit. Because the ledger is committed
input, a pushed revision can make the local hook read and hash an unrelated or
arbitrarily large local regular file. Repeated PASS rows multiply that work.

This violates the architecture's repository-relative evidence contract and
prevents the push path from having a meaningful time/I/O bound.

## Required fix

Production validation must accept only non-symlink evidence contained beneath
the canonical repository root, reject parent traversal, and fail closed before
hashing when the aggregate evidence size exceeds an explicit fixed budget.
Self-test fixtures may use their isolated temporary evidence path. Add adjacent
regressions for traversal, external absolute paths, and oversize evidence.

## Resolution

The consumer canonicalizes the repository root and evidence parent, rejects
production absolute/traversal/outside-root paths and symlink files, sums file
sizes before each hash, and fails above 64 MiB aggregate input. The ledger
self-test now covers all three rejection cases while retaining an explicitly
isolated external-path allowance only inside `--self-test`.

The complete focused contract, including committed-ref and installed-hook
paths, passed in 7.14 seconds at 71,168 KiB peak RSS.
