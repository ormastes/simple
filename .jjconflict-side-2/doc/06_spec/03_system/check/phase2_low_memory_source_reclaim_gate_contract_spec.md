# Phase-2 Low-Memory Source-Reclaim Gate Contract

## Source-contract isolation

The micro probe must avoid `std.spec`, `CompileContext`, HIR, MIR, backend, and
the broad `std.io` facade imports. It extracts exactly one indentation-bounded
body for each target signature and matches singular executable lines within
that body.

The driver contract requires parse, the reclaimability gate, lexer release,
source reclaim, source eviction, and HIR lowering in that order. The
reclaimability body must be exactly guarded by low-memory mode and a non-VHDL
backend. The lexer-release body must contain all seven source-holder resets.

Negative controls intentionally place all formerly accepted tokens in
docstrings or sibling methods. Every negative control must remain false.

## Runtime ownership

The fixture text and its copied alias are passed sequentially to
`rt_string_free`. Pass requires exactly `1` then `0`; no freed alias is read
afterward. Any missing extern, different values, nonzero exit, or missing field
is a hard failure.

## Bounded pure-Simple execution

The shell checker must:

1. resolve a non-symlinked repository release binary and record its absolute
   path and SHA-256;
2. reject Rust-seed, bootstrap-seed, and debug identities;
3. retain exact wrapper-rerun and pinned-child commands;
4. start every child in a new process group;
5. retain at most a 4-KiB head and 4-KiB tail per stream;
6. send TERM then KILL to the whole process group at the deadline;
7. bound FIFO-reader drain after the direct child exits; on drain expiry,
   TERM/KILL the original group and both readers and fail internally with
   status `125` instead of preserving the child status;
8. hash the commands, sources, binary, and bounded logs; and
9. report Stage4 as unused.

## Current status

Blocked. Historical runtime evidence returned `0` then `0` because the deployed
artifact lacked `rt_string_free` and identified as a Rust bootstrap seed. The
repaired checker must not convert that evidence into a pass.
