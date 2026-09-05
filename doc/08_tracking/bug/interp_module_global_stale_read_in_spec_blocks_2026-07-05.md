---
id: interp_module_global_stale_read_in_spec_blocks_2026-07-05
status: OPEN
severity: medium
discovered: 2026-07-05
discovered_by: std.diag (easy-debug-infra P0) implementation + spec work
related: src/lib/nogc_sync_mut/diag.spl
related: test/01_unit/lib/nogc_sync_mut/diag_spec.spl
---

# Module globals mutated in functions read stale from spec `it` blocks

## Summary

When a module-level `var` is mutated only inside that module's own functions
(never assigned directly from the spec file), a spec `it` block that reads
the global directly sees a **stale snapshot** — not the value the module's
own functions would report via an accessor. This is an interpreter/spec
isolation artifact, not a real data race.

```simple
# in module foo.spl
var _g_counter: i64 = 0
fn bump(): _g_counter = _g_counter + 1
fn get_counter() -> i64: _g_counter

# in foo_spec.spl
it "bumps":
    bump()
    expect(_g_counter).to_equal(1)       # BUG: may read stale (0), flaky/wrong
    expect(get_counter()).to_equal(1)    # correct: goes through the accessor
```

Workaround: never assert on a module-level `var` directly from a spec `it`
block — always go through an accessor function defined in the same module.

## Evidence

Documented in `test/01_unit/lib/nogc_sync_mut/diag_spec.spl` header comment
("module globals mutated inside functions are only visible through accessor
functions, not via direct global reads from `it` blocks — all assertions
below go through the module's `dbg_*` accessors") and in
`doc/07_guide/infra/debugging/easy_debug_infra.md` ("Test hooks" section:
"Assert via accessors ... never by reading module globals directly —
interpreter `it` blocks see a stale snapshot of globals"). `std.diag` ships
accessors for every piece of state specifically to work around this
(`dbg_last_emit()`, `dbg_stage_history()`, `dbg_timer_stats(label)`,
`dbg_provenance_mismatches()`, `dbg_deadline_breach_count()`, etc.).

## Impact

Any spec asserting directly on a module-global `var`/`Dict`/`[T]` mutated by
non-spec functions risks silently reading a stale value — a false-green (or
flaky) test result with no error. Forces every stateful module intended to
be spec-tested to expose read accessors for all mutable state.

## Scope

Interpreter-specific: spec `it` block execution context vs module-function
execution context for shared module-level `var` storage.
