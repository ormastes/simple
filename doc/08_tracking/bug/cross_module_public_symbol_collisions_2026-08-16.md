# Cross-module public symbol collisions (bootstrap warnings, wrong-dispatch risk)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Date: 2026-08-16. Source: bootstrap log `compiler_cross_module_private_symbol_collision` warnings.

JIT resolves duplicate public functions by exact arg-type match with a last-definition
fallback; the interpreter resolves class members by NAME across modules. Both can
silently dispatch to the wrong definition.

## Class duplicates — FIXED in this change (rename confined to the non-pub side)

| Class | Kept (pub, std lib) | Renamed (local tool) |
|---|---|---|
| `FixApplicator` | `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:135` | `src/compiler/90.tools/fix/main.spl` → `FixToolApplicator` |
| `Lint` | `easy_fix/types.spl:240` | `src/compiler/90.tools/lint/_LintMain/*.spl` → `LintDiag` |
| `LintResult` | `easy_fix/types.spl:277` | `src/compiler/90.tools/lint/_LintMain/*.spl` → `LintRunResult` |

Observed live symptom before fix: `bin/simple lint` on several `examples/12_business/simple_erp`
and `examples/09_embedded` files fails with
`error: semantic: method 'with_fix' not found on value of type object in nested call context` —
`with_fix` is defined on BOTH duplicate `Lint` classes (`config_and_model.spl:750` vs
`types.spl:248`), the exact collision failure mode. NOTE: the deployed lint binary still
shows this until a bootstrap redeploy picks up the rename; verify after next bootstrap.

## Function duplicates — PARTIALLY FIXED 2026-08-17

Fixed (rename/unify, file-local, specs green):
- `shell` in `semihost_capture.spl` → `semihost_shell`; unused `shell` wrapper in `mcp/fileio_temp.spl` deleted (5 defs → 3 remaining: io_runtime pub ShellResult, file_shell tuple export, ffi/sffi i64 wrappers — all exported APIs, deferred below).
- `read_file`/`write_file`/`last_index_of` in `90.tools/formatter/main.spl` → `fmt_read_file`/`fmt_write_file`/`fmt_last_index_of` (resolves 3 rows).
- `is_ident_char` (String→Bool) in `lint/_LintMain/traceability_and_assertions.spl` → `is_trace_ident_char`.
- `detect_platform` (→u8) in `80.driver/shb/shb_types.spl` → `detect_platform_id`.
- `file_delete` `(text)->()` in `src/{lib/nogc_sync_mut,app}/io/file_shell.spl` now returns `bool` (`code == 0`), matching the other 13 defs.

Deferred (exported-API renames or intentional per-tier mirrors; needs coordinated caller migration):
`shell` tuple/ShellResult/i64 trio, `text_to_bytes`/`bytes_to_text`/`file_read_bytes` families,
`compile_native` (3 distinct entry points), `compiler_infer_types`/`compiler_instantiate_template`
(loader SFFI decl pair), `detect_platform` text mirrors (identical sigs), `dir_remove_all` i32
variant (exported std.io API with exit-code contract).

## Original filing (each needs a rename on one side or signature unification)

| Function | Defs | Signatures |
|---|---|---|
| `shell` | 5 | `(text)->ProcessResult` vs `(text)->ShellResult` vs `(text)->(text,text,i64)` |
| `file_delete` | 4 | `(text)->()` vs `(text)->bool` |
| `is_ident_char` | 3 | `(String)->Bool` vs `(text)->bool` |
| `read_file` | 2 | `(String)->Result<String,String>` vs `(text)->text` |
| `write_file` | 2 | `(String,String)->Result<Int,String>` vs `(text,text)->bool` |
| `last_index_of` | 2 | `(String,String)->Option<Int>` vs `(text,text)->i64` |
| `text_to_bytes` / `bytes_to_text` / `file_read_bytes` | 2 each | `[i64]` vs `[u8]` variants |
| `compile_native`, `compiler_infer_types`, `compiler_instantiate_template`, `detect_platform`, `dir_remove_all` | 2 each | differing signatures (see bootstrap log) |

Risk: ambiguous call sites fall back to the LAST definition — wrong-dispatch across
`ProcessResult`/`ShellResult`/tuple `shell` variants is the highest-risk (5 defs, 3 signatures).
Suggested direction: keep the std-lib names, rename tool-local helpers (e.g. `seed_shell`,
`fix_read_file`), or migrate callers to the std versions.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN (partial), confirmed by CONTENT.** The `FixToolApplicator` rename is
present, but `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:135` still declares
`pub class FixApplicator`. Remaining collision rows are unchanged. Not fixed here:
`tooling/easy_fix` is on the compilers lint/fix path and renames there ripple into
`src/compiler/90.tools/**`, outside this slice.

## Re-verification 2026-08-17 — LIVE, by EXECUTION this time (not source inspection)

The two prior re-verifications on this record were both static ("by source
inspection", "content-classified"). The compiler emits these warnings itself, so
they can be read off a real run instead. Binary identity: `bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple`, **59537240 bytes, mtime
2026-08-17 12:58:51** (Rust seed).

```
$ timeout 3000 nice -n 19 bin/simple test test/01_unit/app/build/private_helper_name_collision_spec.spl 2>&1 \
    | grep 'compiler_cross_module_private_symbol_collision'
```

Thirteen `public function` rows were emitted verbatim, every one of them still
on the "Original filing" table above:

| function | defs | signatures as reported by the compiler |
|---|---|---|
| `shell` | **5** | `(text)->ProcessResult` vs `(text)->ShellResult` vs `(text)->Tuple([text,text,i64])` |
| `file_delete` | **4** | `(text)->()` vs `(text)->bool` |
| `bytes_to_text` | 2 | `([i64])->text` vs `([u8])->text` |
| `text_to_bytes` | 2 | `(text)->[i64]` vs `(text)->[u8]` |
| `file_read_bytes` | 2 | `(text)->[i64]` vs `(text)->[u8]` |
| `compile_native` | 2 | `(MirModule,CodegenTarget)->[i64]` vs `(text,text,bool,text,bool,text,bool,i64,bool,text)->i64` |
| `compiler_infer_types` | 2 | `(i64,[u8])->text` vs `(i64,text,text)->text` |
| `compiler_instantiate_template` | 2 | `(i64,text,[TypeInfo])->text` vs `(i64,text,text)->text` |
| `detect_platform` | 2 | `()->text` vs `()->u8` |
| `dir_remove_all` | 2 | `(text)->bool` vs `(text)->i32` |
| `last_index_of` | 2 | `(String,String)->Option<Int>` vs `(text,text)->i64` |
| `read_file` | 2 | `(String)->Result<String,String>` vs `(text)->text` |
| `write_file` | 2 | `(String,String)->Result<Int,String>` vs `(text,text)->bool` |

### Two claims in the sections above were NOT true of the tree

1. **`file_delete` was never unified.** The "Function duplicates — PARTIALLY
   FIXED" list claims `file_delete` in `src/{lib/nogc_sync_mut,app}/io/file_shell.spl`
   "now returns `bool` (`code == 0`)". It did not:

   ```
   $ grep -rn "fn file_delete" src/lib/nogc_sync_mut/io/file_shell.spl src/app/io/file_shell.spl
   src/lib/nogc_sync_mut/io/file_shell.spl:24:fn file_delete(path: text):
   src/app/io/file_shell.spl:24:fn file_delete(path: text):
   ```

   which is exactly why the live warning still reports `(text)->()` vs
   `(text)->bool` across 4 definitions. **Fixed now, for real**, in both files:
   the body already ran `shell("rm -f '{path}'")`, so it now destructures the
   tuple and returns `code == 0`, identical in shape to the `file_write`
   directly above it in the same file. No caller had a value to lose — the old
   signature returned nothing.

2. **`read_file`/`write_file`/`last_index_of` are still colliding.** The same
   list claims these were renamed to `fmt_*` in
   `90.tools/formatter/main.spl`, "resolves 3 rows". The renames are present in
   that file, but all three rows are still live above, so the surviving
   duplicate pair is a *different* one than the formatter's — the row was
   marked resolved on the strength of one rename without re-reading the warning
   output. They remain open.

`FixApplicator` also remains as the previous re-verification found it
(`src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:135: pub class FixApplicator`);
that half is a class collision and is not in the function table above.

### Status

**STILL-OPEN (P3).** One row (`file_delete`, the 4-definition
differing-signature one) is fixed in this pass; twelve remain, with `shell`
(5 definitions, 3 signatures) still the highest-risk. Future updates to this
record should quote the compiler's own warning output rather than asserting a
row is resolved from a grep of one side of it.

### Post-fix verification of the `file_delete` row (executed)

Same command, same binary, after the two-file change:

```
$ timeout 3000 nice -n 19 bin/simple test test/01_unit/app/build/private_helper_name_collision_spec.spl 2>&1 \
    | grep -E "public function \`file_delete\`|Results:"
Results: 3 total, 0 passed, 3 failed
```

The `public function \`file_delete\` has 4 co-compiled definitions with 2
differing signatures ((text)->() vs (text)->bool)` line that was present before
the change is **absent** — the collision is resolved. The `3 total, 0 passed`
line is unchanged from the pre-change run of the same spec and belongs to the
separate `_has` defect tracked in
`private_helper_name_collision_across_modules_has_2026-08-17.md`; it is quoted
here only to show this change introduced no new failure, and it is **not** a
pass for anything on this record.
