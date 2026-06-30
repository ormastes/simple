# Feature request: iterator protocol for custom types (`for x in <struct>`)

- **Filed:** 2026-06-15 (bytes-foundation Phase-0)
- **Priority:** Medium
- **Area:** language / for-in / traits

## Motivation

Behavior-carrying collection types (e.g. `ByteSpan`, `RingWindow`, future
`Digest`, ring/queue types) cannot be iterated with the natural
`for x in collection:` form. Today `for x in custom_struct` silently iterates
zero times (see bug `for_in_custom_struct_no_iterator_protocol_2026-06-15`),
forcing callers to materialize a backing `[u8]` via `.to_bytes()` or write an
index loop. That defeats zero-copy views and adds boilerplate to every
collection type in the new `common/bytes/` foundation.

## Proposal

Provide an iterator protocol that `for-in` honors for user structs. Either:

1. A standard trait (e.g. `Iterable` with `fn iter() -> Iterator<T>` or a
   `next()`-style contract) that the `for-in` lowering looks up on the
   receiver's type, OR
2. A well-known method hook (`__iter__` / `each`) that `for-in` desugars to.

Until then, the for-in form over a custom struct should be a **compile error**,
not a silent no-op.

## What already works (don't re-spec these)

- `==` value equality on custom structs (structural compare) works.
- `for x in span.to_bytes()` (iterating a real `[u8]`) works.
- Index loops with `get(i)` work.

## Acceptance

- `for b in some_byte_span:` visits each element exactly once.
- A `*_spec.spl` proves the loop body executes `len()` times with correct values.
