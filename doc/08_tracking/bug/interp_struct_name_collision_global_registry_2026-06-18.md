# Interpreter: Same-Named Structs in Different Modules Collide in Global Stores - 2026-06-18

## Severity
P1 (correctness / tooling-blocking). Two modules that each define `struct X`
cannot both be in one program's transitive import closure: the interpreter
resolves the unqualified struct name globally, a later definition shadows the
first, and field access on the first module's own struct fails. `bin/simple
check` (module-scoped type-checker) passes, so the breakage is interpreter-only
and invisible to static checking.

## Component
- Interpreter type/struct resolution (Rust seed, `bin/simple` IS the Rust binary:
  release `cargo build --release --bin simple` -> `target/release/simple`,
  deployed to `bin/release/<triple>/simple`; the error string lives only in
  `compiler_rust`, not `src/compiler/**.spl`).
- Triggering `.spl` collision pair (two distinct `struct WalEntry`):
  - `src/lib/nogc_sync_mut/database/wal.spl` — `WalEntry{ sequence, entry_type, table_name, row_key, data, timestamp }`
  - `src/lib/nogc_sync_mut/storage/shared/wal.spl` — `WalEntry{ lsn, record }`

## Symptom
`bin/simple run src/app/bug_add/main.spl -- ...` aborted with:
```
error: semantic: class `WalEntry` has no field named `sequence`
```
`bug_add` transitively imports BOTH `database.wal` (WalEntry has `sequence`) and
`storage.shared.wal` (WalEntry has only `lsn`/`record`, via the SDN DB -> dbfs ->
storage engine chain). The interpreter binds `WalEntry` to the storage/shared
definition, so `database.wal`'s own `wal_entry_to_line` (`entry.sequence`) fails.

## Minimal reproduce
```
# A) prints "1|Insert|t|k|d|0|..." (works)
use nogc_sync_mut.database.wal.{WalEntry, WalEntryType, wal_entry_to_line}
fn main():
    val e = WalEntry(sequence: 1, entry_type: WalEntryType.Insert, table_name: "t", row_key: "k", data: "d", timestamp: 0)
    print(wal_entry_to_line(e))

# B) identical, but add this import -> "class WalEntry has no field named sequence"
use nogc_sync_mut.storage.shared.wal.{SharedWal}
```
`bin/simple run` A succeeds; B fails. `bin/simple check` passes on both. (Note:
even importing `database.wal` ALONE transitively loads storage.shared.wal via
`database.core -> storage_mode_offload`.)

## Deeper root cause (verified by instrumented probing, 2026-06-18)
NOT a single registry — THREE independent global-short-name stores in the Rust
interpreter, each last-write-wins and polluted non-deterministically by
transitive module loads:
1. The runtime `classes: HashMap<String, Arc<ClassDef>>` (merged by short name in
   `interpreter_module/module_loader.rs` ~947).
2. `MODULE_GLOBALS` (`interpreter_state.rs`) — the bridge function frames use to
   resolve free identifiers; overwritten across imports.
3. The per-module `exports` map built in
   `interpreter_module/module_evaluator/evaluation_helpers.rs::register_definitions`:
   a module's OWN top-level struct and a same-named struct from a TRANSITIVELY
   evaluated import both write `exports["X"]`, and the transitive one wins.
   Confirmed: loading `database.wal` makes `database.wal`'s own
   `exports["WalEntry"]` resolve to storage's `{lsn,record}`.
By construction time NO reachable store (call-frame env, MODULE_GLOBALS, global
classes, or the module's exports) reliably holds the def the importing file
selected — which store is "right" varies by import order (repro A: global map
correct, MODULE_GLOBALS wrong; repro B: both wrong).

## Fix options
1. **Correct fix (interpreter, Rust) — confirmed to be a WIDE refactor.** A
   bounded attempt (add `Option<Arc<ClassDef>>` to `Value::Constructor`, capture
   the module-local def at export sites, prefer it at construction) was
   IMPLEMENTED and reverted: it cannot win because all three stores above are
   polluted before construction, and a MODULE_GLOBALS fallback even regressed the
   previously-working case (repro A). The real fix needs per-file/per-module
   IMPORT-SCOPED type resolution: `WalEntry` in a file must resolve to the def of
   the module that file imported it from, independent of global load order — i.e.
   mirror the HIR/`check` per-module scheme (`import_loader.rs`) in the
   interpreter. Substantial, bootstrap-critical change to the Rust seed.
2. **Pragmatic .spl workaround (APPLIED 2026-06-18).** Rename the storage WAL
   struct so names are unique.

## Workaround applied (2026-06-18) — bug_add unblocked
Renamed `nogc_sync_mut.storage.shared.wal.WalEntry` -> `SharedWalEntry`
(canonical def + internal uses + 4 tier re-export shims
[`gc_async_mut`/`nogc_async_mut` `storage/shared/{__init__,wal}.spl`] + 2
`db/dbfs_engine/wal.spl` facade imports; 7 `.spl` files total). The
`database.wal.WalEntry` (the one with `sequence`) is untouched, so the two
structs no longer share a short name and the interpreter's global stores can't
collide them. Verified: `bin/simple check` OK on storage def + dbfs facade +
`database.core`; `test/02_integration/storage/dbfs/dbfs_engine_wal_spec.spl` 8/8
green; `bug_add` now loads the full SDN-DB chain and writes `bug_db.sdn`
end-to-end (registered `vulkan_per_primitive_submit_wait_throughput` and
`vulkan_present_readback_perpixel_simple_loop`). The underlying interpreter bug
is NOT fixed — this only removes the one name clash that blocked the tooling; any
other duplicate struct name across an import closure will still collide.

## Impact beyond bug_add
Any program whose import closure contains two same-named structs is affected.
`bug_gen` / `bug_resolve` share `bug_add`'s DB chain and were blocked the same
way; they should now load past this clash too.
