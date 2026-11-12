# native-build with an absolute entry under `/test/` collects zero source files (2026-11-12)

Status: OPEN (filed, not fixed). Severity P2.

## Symptom
Stage 2 (aarch64) `native-build <abs>/test/.../x.spl` fails at `phase=load_sources`:
`compiler entry '<abs>' collected zero source files: the entry must be a path to a .spl file ...`.
The same file given RELATIVE to the cwd builds and runs.

## Matrix (binary pinned-f8ad54b28467 stage2, cwd = pinned dir, hello-world, SIMPLE_BOOTSTRAP=1)
| entry | result |
|---|---|
| `zzh.spl` (repo root, relative) | OK |
| `test/zz_abs/zzh.spl` (relative) | OK |
| `src/zz_abs/zzh.spl` (relative) | OK |
| `<abs>/zzh.spl` (repo root) | OK |
| `<abs>/test/zz_abs/zzh.spl` | **FAIL zero sources** |
| `<abs>/src/zz_abs/zzh.spl` | OK |
| `<scratch outside repo>/h.spl` | OK |

So it is not "absolute paths in the source root" but any path whose text contains `/test/`
(also `/tests/`, `/testdata/`, `/verification/`, and `/doc/` outside `src/`). A relative
`test/x.spl` has no leading `/` and slips past the substring check, which is why the relative
spelling "works". (A relative `sub/test/x.spl` would fail too.) Scratch dirs that happen to be
outside any `test/` dir pass, matching the second observer.

## Root cause
`SIMPLE_COMPILER_TRACE=1` shows no `[collect_sources]` and no `[explicit-source]` line, i.e. the
entry went through the import-closure collector, not the explicit one:

- `src/compiler/80.driver/driver_source_pipeline_loading.spl:917-923`: for the entry input,
  `if explicit_entry_closure or native_group_inputs.len() > 0: _driver_collect_explicit_compiler_source`
  `else: _driver_collect_entry_import_source`. `explicit_entry_closure` (line 356) is true only when
  `compiler_source_entry` config is set; here the entry arrived via `SIMPLE_NATIVE_BUILD_ENTRY`
  (line 329-334), so the else branch runs.
- `src/compiler/80.driver/driver_entry_closure_core.spl:1956` (`_driver_collect_entry_import_source_untimed`):
  `normalized.contains("/test/") or ... "/tests/" ... "/testdata/" ... is_repository_doc ... "/verification/"`
  returns `[]`. That production-closure packaging filter is meant for imported modules, but is applied to
  the requested entry itself. Result is empty -> line ~1002 error in the pipeline file.

## Fix options
1. (1 line, preferred) at `driver_source_pipeline_loading.spl:920` also use the explicit collector when
   the entry came from `SIMPLE_NATIVE_BUILD_ENTRY`: `if explicit_entry_closure or native_group_inputs.len() > 0 or native_entry_env != "":`.
   The explicit collector (driver_entry_closure_core.spl:1882) has no packaging filters, matching the
   neighbouring comment ("Applying those filters to the explicit entry makes a real, existing file disappear").
2. Make `_driver_collect_entry_import_source` skip the filter for the root entry.
Not implemented here: the only test surface is the pipeline method (needs a full stage2 redeploy to
observe), so no honest red/green spec on the seed was possible; verify by re-running the matrix row above.
