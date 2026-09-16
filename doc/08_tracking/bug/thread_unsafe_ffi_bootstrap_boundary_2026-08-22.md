# Thread unsafe FFI bootstrap boundary

## Failure

The source-matched cycle-4 closure reported one failed body in
`ThreadPool.new` and twenty failed bodies in `thread_sffi.spl`. The affected
bodies all contained lexical `unsafe(capabilities: [ffi])` blocks. Restricted
admitted bootstrap builders can misparse that form and lower `ffi` as an
unresolved global.

## Repair

Each raw runtime call now lives in a private function-level `@unsafe` leaf.
Public thread, mutex, condition-variable, and pool interfaces remain safe and
retain their existing handle validation, spawn failure, and ownership rules.
Every new leaf makes exactly one direct extern call. It contains no allocation,
array construction, collection mutation, aggregate copy, loop, or branch. The
thread-pool constructor also removes the temporary initialized scalar that was
immediately overwritten.

## Focused evidence

The existing cycle-4 build is the reproducing probe. One combined focused
retry compiled the current `thread_sffi.spl` and `thread_pool.spl` owners with
zero owner body failures, zero `ffi` `GlobalLoad`, and stub fallback disabled.
The synthetic entry body itself was rejected independently, so this is focused
owner evidence rather than executable or Stage-4 acceptance evidence.

- builder: admitted Pure-Simple Stage-2 `stage2-admitted/simple`
- backend/mode: Cranelift/dynload
- elapsed: 1.16 seconds
- maximum RSS: 163,384 KiB
- owner body failures: 0 (previously 21)
- retry count: 1

Receipts are retained under
`build/native_probe/mcdc_cycle4_threads/{retry.log,retry.time}`. The static
ownership preflight also rejects lexical unsafe blocks in both repaired owners.
