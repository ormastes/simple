# Static lock-level owner research

Target: `release_phase3` at `f5c0f468556` (remote verified 2026-10-25).
Selected requirement: REQ-MC-006, ASYNC-LOCK-ORDER, and item 10 of
`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`.

The target has generic `@name(...)` declaration grammar but no lock-level
metadata/checker. Runtime TSan lock graphs are separate evidence. The existing
runtime audit commit `100da986c9e` does not implement this static requirement.

The canonical physical API is
`src/lib/nogc_sync_mut/concurrent/mutex.spl`. `Mutex.with_lock` and
`mutex_with_lock` hold the lock during an immediate callback and store its
result. `mutex_with_lock_keeping` stores its separate keep argument instead;
both values need proof. Manual lock/try_lock return protected values, with
separate unlock; no RAII guard exists. The async facade reexports a synchronous
backend and does not establish scheduler suspension support.

Parser ownership is `_ParserDecls/enum_module_body.spl`,
`_ParserDecls/fn_struct_decls.spl`, and `parser_decls_use.spl`. The shared
frontend covers interpretation; native assembly has a separate fresh parse
and cached arena restoration path. All require the same admission check.
Flat snapshots need a version bump, restored-ID validation and transient owner
promotion. Function parameter arrays must be copied when collecting locals.

Astra reviewed scope and implementation adversarially. No independent
external locking semantics are imported: the source contracts above define
the supported API and its precise callback lifetime.
