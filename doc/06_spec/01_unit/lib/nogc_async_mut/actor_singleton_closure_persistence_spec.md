# Actor singleton closure persistence

Source: `test/01_unit/lib/nogc_async_mut/actor_singleton_closure_persistence_spec.spl`.

Authored manual; doc generation and execution are pending a qualified
self-hosted runtime. **TEST_BLOCKED**, not generated verification evidence.

1. Register a named handler, spawn through the production facade, and reacquire
   the singleton. Require the actor count increment and retained handler stats.
2. Repeat with a lambda literal to preserve the historical closure-field trigger.
3. Repeat with an empty handler table as the adjacent singleton-path control.

Run: `<qualified-selfhosted-runtime> test test/01_unit/lib/nogc_async_mut/actor_singleton_closure_persistence_spec.spl --mode=interpreter`.

Expected inventory: three scenarios, zero failures. No current result claimed.
