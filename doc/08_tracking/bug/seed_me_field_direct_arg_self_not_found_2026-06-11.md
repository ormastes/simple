# Seed interpreter: `me.field` as direct arg to a nested `me fn` call → `self` not found

- **Status:** open (workaround in place at all current call sites)
- **Found:** 2026-06-11 while fixing
  `dbfs_checkpoint_facade_spec_self_not_found_2026-06-11.md`
- **Severity:** medium — silent class of interpreter-mode failures; the error
  message (`semantic: variable 'self' not found`) points at the callee, not
  the offending argument expression.

## Minimal repro

```
# Fails in interpreter mode:
me fn query(q: AttrQuery) -> AttrQueryResult:
    ids = me._query_index(me.size_index, q.op)   # me.field as direct arg

# Works:
me fn query(q: AttrQuery) -> AttrQueryResult:
    var idx_copy = me.size_index
    ids = me._query_index(idx_copy, q.op)        # copy to local first
```

## Notes

- This is a Rust seed (interpreter) bug, distinct from the plain-`fn self.`
  strictness (which is by-design: mutable methods must be `me fn`).
- Workaround applied 2026-06-11 in
  `src/lib/nogc_sync_mut/db/dbfs_engine/attr_index.spl` (`query`,
  `_remove_from_field_index`).
- Fix belongs in the seed's method-call argument evaluation (receiver context
  lost while evaluating `me.field` argument expressions). Per repo rule, Rust
  seed edits need explicit authorization — fix when next seed batch is opened,
  and add an interpreter regression test alongside.
