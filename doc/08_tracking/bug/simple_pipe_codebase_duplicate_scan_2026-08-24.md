# `simple_pipe` codebase duplicate scan and child startup

**Status:** Open — compatibility design complete; implementation blocked on a
shared freshness/order contract.

## Live cost

`handle_simple_pipe_codebase` runs bounded `rg`, then starts a child Simple
process for workspace symbols. The child loads `query.spl` and independently
searches `src`. A request pays compiler/process startup, two overlapping tree
traversals, two captures, and repeated split/count/render allocations. SQL mode
may add another child.

## Compatibility boundary

- Raw search accepts arbitrary case-sensitive regex, rewrites it by `kind`,
  targets `scope` or exact `file`, returns 51 raw lines, and collapses several
  error/no-output states.
- Workspace symbols always target `src`, sanitize the query, recognize a wider
  declaration grammar, retain 200 candidates, emit 100 JSON symbols, and expose
  a child exit/header.
- `kind` affects raw matching and the symbol header only; `requester` currently
  has no symbol effect; traversal order is observable.

The capped raw output cannot supply equivalent symbols. A combined regex without
branch framing cannot prove which raw regex matched, and another regex engine
risks dialect drift. TTL or MCP-write-only caches become stale after editor, Git,
or external filesystem changes.

## Target architecture

Raw `rg` remains authoritative and performs one O(B_scope) content scan per
request. An MCP-owned declaration-only `src` index removes the second recursive
symbol content scan and child compiler startup. It stores normalized path,
stable traversal ordinal, declaration records, and freshness receipts; queries
preserve the case-sensitive post-declaration-payload grep prefilter/200 cap,
followed by the case-insensitive name filter/100 cap and existing header.

Freshness requires an authoritative filesystem watcher/change journal. Create,
modify, delete, and rename events update only affected declaration records;
watcher overflow, loss, permission uncertainty, or startup without a complete
checkpoint forces a full declaration-index rebuild. A per-request metadata walk
may be a fallback hint but cannot prove freshness: same-size, same-timestamp
external rewrites are otherwise invisible. Incomplete validation falls back to
the current symbol producer, never stale output.

Eliminating the remaining warm raw scan is separately blocked on retaining full
source contents plus an rg-compatible regex/error/timeout implementation with
authoritative invalidation. Bounded metadata alone cannot answer arbitrary
regex. A compiled shared-walk envelope is viable only if it machine-frames
branch identity and preserves independent caps; it cannot wrap today's scans.

## Acceptance evidence

- zero `simple run src/app/cli/query.spl` children for healthy indexed requests;
- one authoritative raw content walk per request, zero additional recursive
  symbol content walks, and changed-file-only symbol-index reads;
- byte-compatible raw and symbol fixtures across regex metacharacters, every
  kind/scope/file combination, empty/sanitized queries, 51/200/100 boundaries,
  stable grep traversal ordering, invalid-regex/no-output stderr collapse,
  missing paths, the raw 15-second timeout, and symbol header/exit emulation;
- external same-size rewrites, edit/create/delete/rename, Git checkout, watcher
  overflow/loss, symlinks, permissions, and read-failure fixtures;
- degraded-mode evidence that watcher uncertainty invokes the authoritative
  producer rather than returning stale indexed symbols;
- parity in both `src/app/mcp` and the `src/lib/nogc_async_mut/mcp` provider;
- measured cold/warm latency, child count, bytes read, allocation bytes, and max
  RSS on a representative repository;
- rollback confined to the MCP snapshot/provider; standalone query/LSP remains
  authoritative.

## Immediate mitigation

MCP JSON escaping and bounded first-line rendering no longer copy growing text
prefixes. This reduces parent allocation traffic but does not close this bug.
