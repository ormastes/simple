# `type X = Y` does not resolve as a static-call receiver — `X.new()` sees nil

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

A type alias works as a *type annotation* but not as a *static-call receiver*.
The alias name evaluates to `nil`, so any `Alias.static_method()` fails.

Minimal repro (`bin/simple test <file>`):

```simple
use std.storage.shared.wal.{SharedWal}
use std.db.dbfs_engine.wal.{DbfsWal}      # type DbfsWal = SharedWal

describe "alias static dispatch":
    it "direct struct name works":
        val w = SharedWal.new()
        expect(w.durable_lsn).to_equal(0)
    it "alias name works":
        val w = DbfsWal.new()
        expect(w.durable_lsn).to_equal(0)
```

Actual:

```
  ✓ direct struct name works
  ✗ alias name works
    semantic: method `new` not found on type `nil` (receiver value: nil)
Results: 2 total, 1 passed, 1 failed
```

Expected: both pass. `DbfsWal` is declared `type DbfsWal = SharedWal` at
`src/lib/nogc_sync_mut/db/dbfs_engine/wal.spl:13` and is exported on line 15.

Note the receiver is `nil`, not "a type with no such method" — the alias name
resolves to no value at all, so the failure is in *name resolution*, not in
static-method lookup.

## Root cause

Type aliases are captured at parse time but never reach any value/receiver
resolution path.

- Captured into `module.type_aliases` at
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:621`
  (the TAL1 lane added by `type_alias_declarations_discarded_at_parse_2026-07-29.md`).
- The **only** consumers of `module.type_aliases` are the lint/semantic alias
  registry (`src/compiler/35.semantics/lint/semantic_api/alias_registry.spl:211`)
  and the VHDL codegen path
  (`src/compiler/80.driver/driver_compile_vhdl_codegen.spl:112`). Nothing binds
  the alias name as a resolvable receiver.
- The error text is emitted by the **Rust bootstrap seed** interpreter at
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1576`, which is what
  `bin/simple test` actually evaluates spec bodies on (`bin/simple` prints the
  "Rust-built Simple binary is a bootstrap seed only" banner).

So the alias is dropped on both halves: the pure-Simple frontend records it but
routes it nowhere, and the seed interpreter never learns of it.

## Why not fixed now

The fix that would turn the tests green has to land in the Rust seed
interpreter's name-resolution table, and repo rules put that off-limits
(`.claude/rules/` — "Fix .spl not Rust"; "Seed is bootstrap-only"). Implementing
it on the pure-Simple side instead is a real feature (thread `type_aliases`
through export + receiver resolution), not a small change, and it would **not**
turn these tests green today, because the seed is the binary that runs them.

Filing rather than papering over. What was done instead, and is safe on its own
merits: the two product call sites that constructed *through* the alias now call
the canonical struct directly, matching what the sibling module
`src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint.spl` already does
(`SharedCheckpointRing.new_persistent()` etc.):

- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:419,463` —
  `DbfsWal.new()` → `SharedWal.new()`.

That took `test/02_integration/storage` from 143 to 106 failures. The alias
itself is still broken for every external caller, including the specs that
exercise the back-compat names directly
(`dbfs_engine_intent_log_spec.spl` → `IntentLog.new()`,
`dbfs_engine_checkpoint_ring_spec.spl` → `CheckpointRing.new_persistent()`,
still ~12 failures). Those specs are correct as written and were deliberately
left red rather than rewritten onto the canonical names, which would have hidden
this defect.

## Related

- `type_alias_declarations_discarded_at_parse_2026-07-29.md` — the parse-side
  capture this bug sits downstream of.
- `type_alias_swapped_winner_is_inert_2026-08-01.md`
- `flat_ast_export_from_and_type_alias_loss_2026-07-27.md`
