# Parallel Applications

Simple parallel code follows one default convention: the owner keeps canonical
mutable state; children read immutable input or receive explicit ownership;
children create independent results; the owner validates and commits them.

## Current contract surface

The repository now provides common vocabulary for transfer envelopes, storage
plans, access paths, parent-commit ordering, and assurance policy:

- child-created outputs are the preferred transfer direction;
- parent-owned mutable state is an explicit consuming move;
- process, remote, and device boundaries reject an ordinary owned in-memory
  region; they require an encoded/immutable handle or device lease;
- unknown dynamic ranges overlap until proven otherwise;
- external ABI/wire/MMIO storage remains pinned.

Critical policy denies implicit parent-to-child moves and dynamic transport, and
requires bounded mailboxes, deterministic commits, and frozen layout receipts.

## Status

These are common/compiler contract foundations, not a claim that every current
actor, process, thread-pool, generic channel, or backend layout path already
enforces them. Runtime codecs, typed bounded public transport, structured task
groups, physical layout lowering, and end-to-end process/device evidence remain
work-package gates. Consult the receipt and the matching runtime gate before
relying on a path in production.

## Recommended shape

```simple
val snapshot = owner.snapshot()
val results = TaskGroup.map(parts, snapshot, build_child_result)
owner.commit(results)?
```

Do not use a raw pointer or unclassified dynamic object as a cross-domain
payload. Do not infer that two different index variables are disjoint.
