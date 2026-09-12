# `bin/simple lint` SEGVs on unit spec files

- Status: OPEN (2026-09-12)
- Area: app/lint, compiler (JIT symbol resolution)
- Severity: medium (every `.spl` spec is unlintable; a lane told to "lint the touched files"
  gets a core dump, not a verdict, and a crash is easy to misread as a clean run because
  the warnings printed just before it look like ordinary output)
- Found by: RUNNER-DEGRADE lane while linting its own touched files. Not fixed — out of
  this lane's scope, and it reproduces on files this lane never touched.

## Symptom

```
$ bin/simple lint test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl
...
warning: public function `shell` has 4 co-compiled definitions with 2 differing signatures
  ((text)->ProcessResult vs (text)->i64); JIT call sites resolve by exact arg-type match ...
Segmentation fault (core dumped)
$ echo $?
139
```

No `Lint completed with N error(s)` verdict line is ever printed. The process dies after
emitting the `compiler_cross_module_private_symbol_collision` warnings.

## It is not the file under test

Reproduced on two unrelated specs, one of which this lane never edited:

| file | exit |
|---|---|
| `test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl` (untouched, at origin/main) | 139 |
| `test/01_unit/app/test_runner_new/smf_compile_error_degrades_spec.spl` (new this lane) | 139 |

Source files in the same run lint cleanly and print a verdict:

| file | exit | verdict |
|---|---|---|
| `src/app/test_daemon/light_protocol.spl` | 0 | `0 error(s), 1 warning(s)` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl` | 0 | `0 error(s), 9 warning(s)` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | 0 | `0 error(s), 18 warning(s)` |

So the crash is specific to linting a **spec** file, not to any particular spec.

## Likely lead

The last thing printed before every crash is the duplicate-definition warning for
`process_wait` / `shell` — public names with several co-compiled definitions and DIFFERING
signatures (`(i64)->i64` vs `(i64,i64)->i64`; `(text)->ProcessResult` vs `(text)->i64`).
The warning text itself says JIT call sites "fall back to the last definition when types
are ambiguous — a fallback hit may still dispatch to the wrong one". Dispatching a
`(text)->ProcessResult` call into a `(text)->i64` body would explain a SIGSEGV exactly
here. Specs reach those symbols through `use std.spec.*`, which is why source files under
`src/` do not crash.

## Repro

```
readlink -f bin/simple    # Rust seed, sha256 prefix 3d120a6f
bin/simple lint test/01_unit/app/test_runner_new/no_examples_fail_closed_spec.spl; echo $?
```
Expected: a `Lint completed with ...` verdict and exit 0 or 1. Actual: exit 139.
