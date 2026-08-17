# `type X = Y` does not resolve as a static-call receiver — `X.new()` sees nil

**Status:** OPEN — architectural (needs a Rust-seed interpreter name-resolution
change, out of scope per repo rules; re-confirmed 2026-08-10)
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

## Re-verification (2026-08-10)

Confirmed the root cause still holds: `bin/simple` is a symlink to
`bin/release/x86_64-unknown-linux-gnu/simple` (the Rust bootstrap seed), and
`bin/simple test` on the exact repro spec in this doc still routes spec-body
evaluation through the seed. A live re-run of the repro
(`test/02_integration/storage/dbfs/dbfs_engine_intent_log_spec.spl`, which
depends on the same alias-resolution path) was attempted but hit this
environment's known long-startup/timeout ceiling before printing a verdict
line, so it is not usable as fresh pass/fail evidence either way (consistent
with the documented "long test runs get killed before a verdict" measurement
trap) — this re-verification instead relies on source audit, which is
conclusive for the mechanism.

Also checked whether the pure-Simple HIR layer has grown a receiver-resolution
path for `module.type_aliases` since this doc was filed: it has grown
additional *consumers* of `type_aliases` in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` and
`src/compiler/20.hir/hir_lowering/module_surface.spl` (import/symbol-kind
resolution, e.g. resolving an imported name's `item_kind` to `"type_alias"`).
None of this reaches static-call **receiver** value resolution, and none of it
matters for `bin/simple test` regardless, since spec bodies are evaluated by
the Rust seed interpreter, not this pure-Simple HIR/MIR pipeline. The doc's
"only consumers are lint + VHDL" claim is therefore now slightly stale for the
pure-Simple side, but the bug and its architectural blocker are unchanged.

## Related

- `type_alias_declarations_discarded_at_parse_2026-07-29.md` — the parse-side
  capture this bug sits downstream of.
- `type_alias_swapped_winner_is_inert_2026-08-01.md`
- `flat_ast_export_from_and_type_alias_loss_2026-07-27.md`

## Re-verification 2026-08-17

Re-read `src/compiler/35.semantics/lint/semantic_api/alias_registry.spl` in
full. `alias_registry_populate` (line 211) still only builds a name -> immediate
target lookup table for lint/VHDL consumption; there is still no code path in
this file, or anywhere reachable from `35.semantics`, `30.types`, `90.tools`, or
`95.interp`, that binds a type-alias name as a resolvable static-call receiver
VALUE. That resolution (the actual bug) is produced by the Rust bootstrap seed's
interpreter method dispatch (`src/compiler_rust/compiler/src/interpreter_method/mod.rs`),
which remains out of scope per repo rules ("Seed is bootstrap-only").

No pure-Simple file in this worker's scope lock owns receiver-value resolution
for identifiers, so there is nothing to change here.

**Verdict: BLOCKED (architectural — fix belongs in the Rust seed interpreter's
name-resolution table, explicitly out of scope). No code change made.**
