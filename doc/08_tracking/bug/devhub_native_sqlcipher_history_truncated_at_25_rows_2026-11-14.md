# Native devhub returns only the first 25 rows of a multi-page SQLCipher table

**Status:** verification-pending
**Found:** 2026-11-14
**Severity:** P1 — silent data loss on read, native only (interpreter correct)

## Symptom

`devhub messenger messages --room 2` on the checked-in dense fixture
(`test/fixtures/database/sqlcipher4/dense_multipage.sqlcipher4`, 9 pages, room 2
holds 41 messages, ids 16..56) returns all 41 rows through the interpreter and
exactly 25 (ids 16..40) from a native build. Exit code 0, no warning.

```
limit=24 -> 24 rows      limit=26 -> 25      limit=41 -> 25
limit=0  -> 25           no --limit -> 25
```

## Root cause — a miscompiled clamp constant, not the b-tree

The b-tree walk is correct natively: the page trace is identical in both lanes
(root 4, leaves 7/8/9, 46 rows decoded). The rows are dropped afterwards by the
history clamp in `src/app/devhub/messenger/adapter/db_common.spl`, which bounds
the request at `MESSENGER_DEFAULT_MAX_READ_BATCH`. That constant is declared
`val MESSENGER_DEFAULT_MAX_READ_BATCH = 200` with no type annotation, in another
module.

The defect is general and is in the Rust seed's HIR import loader: **any
unannotated integer `val`/`static` imported across modules is read natively as
`value >> 3`.** The declaring module infers `i64` from the literal and stores
the raw word. The importing module typed the same global `Any`, so native code
read the raw word as a tagged value and untagged it: 200 >> 3 = 25. A `: i64`
annotation, or a read from the declaring module itself, gives 200. Unannotated
`bool` and `text` literals had the same type disagreement.

The earlier wording here ("the loss starts where the table b-tree needs more
than its first leaf pages", and "there is no 25 in the messenger sources") was
a wrong lead: 25 is 200 >> 3, and 41 rows was simply the first case above 25.

## Fix

`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`: an imported
`val`/`static` with no annotation now gets the type the declaring module infers
for it (`bool`, `text`, or `i64` for a constant-evaluable integer expression);
anything else stays `Any` as before. `try_const_eval` in
`hir/lower/module_lowering/module_pass.rs` became `pub(crate)` so both sides use
one predicate.

Not covered: an unannotated imported float literal still types as `Any` in the
importer. It was not probed natively.

## Evidence

Minimal repro (`val UNTYPED_CAP = 200` in one module, read in another), native,
Windows, llvm-mingw 20260922:

```
seed 97728d94d5f (before): untyped=25  small=25  direct=25  interp=25  sum=26
seed with fix   (after):   untyped=200 small=30  direct=200 interp=200 sum=201
```

Rust unit test `imported_unannotated_literal_val_keeps_declaring_module_type`:
before `left: TypeId(14) right: TypeId(5)`, after `1 passed`; `import_loader`
filter `19 passed; 0 failed`.

Regression spec `test/01_unit/compiler/imported_untyped_module_val_native_spec.spl`
(support module `test/support/untyped_module_vals.spl`): interpreted
`Results: 4 total, 4 passed, 0 failed`.

Native devhub rebuilt with the fixed seed:

```
DEVHUB_NATIVE_BIN=<abs>/build/nb/devhub_g.exe simple test test/03_system/app/devhub/messenger/messenger_read_verbs_history_edges_spec.spl
```

```
seed 97728d94d5f devhub (before): expected 25 to equal 41 — Results: 8 total, 7 passed, 1 failed
fixed seed devhub (after):        Results: 8 total, 8 passed, 0 failed
interpreted:                      Results: 8 total, 8 passed, 0 failed
```

Also native on the fixed build: `native_binary_sqlcipher_read_spec.spl` 2/2,
`native_binary_sqlcipher_open_spec.spl` 4/4. The new regression spec has not
been run through a native test lane; its native evidence is the minimal repro.
