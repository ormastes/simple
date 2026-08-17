# Interpreter: struct-in-Dict field with a closure-typed sibling field reads back nil

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom

`src/lib/nogc_async_mut/actors/actor.spl`'s documented public API `spawn_actor(handlers)`
(module-level convenience wrapping the `ActorRuntime` singleton) silently loses the
spawned actor: after `spawn_actor(handlers)` returns, a fresh `get_actor_runtime()` call
reports the actor `not found` and `actor_count() == 0`. The actor's mailbox is never
reachable, so `worker.send(...)` followed by `rt.run()` never invokes any handler.

## Root cause (bisected, not yet fixed)

Not a logic bug in `actor.spl`. Reproduced with 10 progressively-isolated minimal repro
files. The defect requires the *combination* of:

1. A struct value stored inside a `Dict<K, V>` field of a singleton/module-level struct.
2. `V` (the dict's value type) itself has a `fn(...) -> ...`-typed field that was
   populated from a `\args: ...` lambda literal earlier in the same function.

Under that combination, fetching the struct back from the dict via a second, independent
accessor call reads back `nil` for the key that was just inserted — even with no
`Option`/`match` involved (plain module `var`, direct getter/dict access). Removing the
lambda-typed field, or removing the two-level struct-in-dict-in-struct nesting, makes the
value persist correctly.

Likely area: how the tree-walk interpreter deep-copies/aliases structs containing boxed
closures when read back out of a `Dict` value slot.

## Reproduction

Minimal repros (ephemeral, not committed) were built at:
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/895f85cb-815f-448b-86ed-4708de028caa/scratchpad/probe_actor{2,3,5,6,9,10}.spl`
— these are session-scratch and may not persist; re-derive from the pattern above if
needed (struct-in-Dict-in-struct where the leaf struct has a lambda-literal field).

## Next steps

- Reproduce fresh under `bin/simple test` with a spec committed under
  `test/01_unit/lib/nogc_async_mut/actors/` once someone picks this up.
- Bisect further: does it repro under native/JIT engines too, or only the interpreter?
  (Not checked this round — investigation stopped at interpreter-level repro.)
- Once root-caused in the interpreter's struct/Dict/closure handling, fix there — do NOT
  patch around it in `actor.spl` (e.g. by avoiding lambda-typed fields), since that masks
  an engine defect that likely affects other callers with the same shape.
