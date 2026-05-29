# Constant callbacks use wildcard lambda short grammar

Date: 2026-05-27

## Symptom

After migrating safe single-expression lambdas to placeholder grammar, the
remaining simple callback hits are mostly already-minimized wildcard callbacks:

```simple
items.map(\_: 0)
headers.map(\_: "---")
future.then(\_: HostFuture.pending())
pipeline.filter(\_: true)
```

The supported compact form for this case is the wildcard lambda `\_:`. It means
"ignore the callback argument and return this expression" while still passing a
function to `map`, `filter`, `then`, and related higher-order APIs.

## Impact

The short-grammar fixer can safely convert `\x: constant` to `\_: constant`.
It must not rewrite existing `\_:` callbacks to a non-lambda expression. Doing
so would pass the constant value itself rather than a callback.

## Resolution

Documented `\_:` as the canonical compact callback form for ignored callback
arguments. Remaining `\_:` hits in short-grammar migration scans are intentional.
