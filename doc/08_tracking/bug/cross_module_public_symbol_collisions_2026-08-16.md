# Cross-module public symbol collisions (bootstrap warnings, wrong-dispatch risk)

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

## Function duplicates — FILED, not fixed (each needs a rename on one side or signature unification)

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
