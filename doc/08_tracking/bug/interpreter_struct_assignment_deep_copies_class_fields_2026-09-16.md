# Interpreter: struct assignment deep-copies class fields, breaking shared state

Date: 2026-09-16
Status: OPEN

## Observed

`actor_mailbox_close_spec.spl` fails: copying an actor handle (struct holding
a class field `ActorMailboxState`) and calling `close()` on the copy must
close the ONE shared mailbox. Minimal repro prints `false true` (close visible
on original only after the copy's mutation, i.e. the class field was deep-copied
instead of shared):

```simple
val original = ...            # struct with class field
val copied = original
copied.close()                # mutates a copy of the class field
original.is_closed()          # false (expected true)
```

## Impact

Any struct-with-class-handle value semantics design (the actor mailbox uses
exactly this to share `ActorMailboxState` across clones) silently breaks:
mutation through one alias is not observed through another.

## Expectation

Class instances are reference semantics: assigning a struct copies the struct
but the class field must remain the SAME object.

## Unblock condition

Fix value copy semantics in the interpreter for class-typed fields. Seed-side
(Rust) interpreter; re-verify with the minimal repro above, then re-run
`test/01_unit/lib/nogc_async_mut/actor_mailbox_close_spec.spl`.
